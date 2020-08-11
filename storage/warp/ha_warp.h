/*  Copyright (c) 2003, 2018, Oracle and/or its affiliates. All rights reserved.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License, version 2.0,
   as published by the Free Software Foundation.

   This program is also distributed with certain software (including
   but not limited to OpenSSL) that is licensed under separate terms,
   as designated in a particular file or component or in included license
   documentation.  The authors of MySQL hereby grant you an additional
   permission to link the program and your derivative works with the
   separately licensed software that they have included with MySQL.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License, version 2.0, for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA */
#ifndef HA_WARP_HDR
#define HA_WARP_HDR
#define MYSQL_SERVER 1
#include "sql/sql_class.h"
#include "sql/sql_lex.h"
#include "sql/item.h"
#include "sql/item_cmpfunc.h"

#include <sys/stat.h>
#include <sys/types.h>
#include <dirent.h>
#include <string.h>

#include "my_dir.h"
#include "my_inttypes.h"
#include "my_io.h"
#include "sql/handler.h"
#include "sql_string.h"
#include "sql/dd/dd.h"
#include "sql/dd/dd_table.h"
#include "sql/dd/dd_schema.h"
#include "sql/abstract_query_plan.h"

#include <fcntl.h>
#include <mysql/plugin.h>
#include <mysql/psi/mysql_file.h>
#include <algorithm>

#include "map_helpers.h"
#include "my_byteorder.h"
#include "my_dbug.h"
#include "my_psi_config.h"
#include "mysql/plugin.h"
#include "mysql/psi/mysql_memory.h"
#include "sql/field.h"
#include "sql/sql_class.h"
#include "sql/system_variables.h"
#include "sql/table.h"
#include "template_utils.h"

#include "sql/log.h"


#include <fstream>  
#include <iostream>  
#include <string> 
#include <atomic>
#include <vector>
#include <thread>
#include <forward_list>
#include <unordered_map>
#include <time.h>

#include "include/fastbit/ibis.h"
#include "include/fastbit/query.h"
#include "include/fastbit/bundle.h"
#include "include/fastbit/tafel.h"
#include "include/fastbit/array_t.h"
#include "include/fastbit/mensa.h"
#include "include/fastbit/resource.h"
#include "include/fastbit/util.h"

#include "sql/sql_thd_internal_api.h"

#include "sparse.hpp"
// used for debugging in development
#define dbug(x) std::cerr << __LINE__ << ": " << x << "\n"; fflush(stdout)

/*
  Version for file format.
  1 - Initial Version. That is, the version when the metafile was introduced.
*/
const uint16_t WARP_VERSION = 2;

#define BLOB_MEMROOT_ALLOC_SIZE 8192

static const char *ha_warp_exts[] = {
  ".data",
  NullS
};

/* engine variables */
static unsigned long long my_partition_max_rows, my_cache_size, my_write_cache_size;//, my_lock_wait_timeout;

static MYSQL_SYSVAR_ULONGLONG(
  partition_max_rows,
  my_partition_max_rows,
  PLUGIN_VAR_RQCMDARG,
  "The maximum number of rows in a Fastbit partition.  An entire partition must fit in the cache.",
  NULL,
  NULL,
  1024 * 1024,
  1024 * 1024,
  1ULL<<63,
  0
);

static MYSQL_SYSVAR_ULONGLONG(
  cache_size,
  my_cache_size,
  PLUGIN_VAR_RQCMDARG,
  "Fastbit file cache size",
  NULL,
  NULL,
  1024ULL * 1024 * 1024 * 4,
  1024ULL * 1024 * 1024 * 4,
  1ULL<<63,
  0
);

static MYSQL_SYSVAR_ULONGLONG(
  write_cache_size,
  my_write_cache_size,
  PLUGIN_VAR_RQCMDARG,
  "Fastbit file cache size",
  NULL,
  NULL,
  1000000,
  1000000,
  1ULL<<63,
  0
);

/*
static MYSQL_SYSVAR_ULONGLONG(
  lock_wait_timeout,
  my_lock_wait_timeout,
  PLUGIN_VAR_RQCMDARG,
  "Timeout in seconds a WARP transaction may wait "
  "for a lock before being rolled back.",
  NULL,
  NULL,
  1,
  50,
  ULONG_MAX,
  0
);
*/

static MYSQL_THDVAR_ULONG(lock_wait_timeout, PLUGIN_VAR_RQCMDARG,
                          "Timeout in seconds a WARP transaction may wait "
                          "for a lock before being rolled back.",
                          nullptr, nullptr, 50, 0, ULONG_MAX, 0);


SYS_VAR* system_variables[] = {
  MYSQL_SYSVAR(partition_max_rows),
  MYSQL_SYSVAR(cache_size),
  MYSQL_SYSVAR(write_cache_size),
  MYSQL_SYSVAR(lock_wait_timeout),
  NULL
};


struct WARP_SHARE {
  std::string table_name;
  uint table_name_length, use_count;
  char data_dir_name[FN_REFLEN];
  uint64_t next_rowid = 0;  
  mysql_mutex_t mutex;
  THR_LOCK lock;
};

class warp_pushdown_information {
 public:
 std::unordered_map<std::string, std::string> filters;
 std::unordered_map<std::string, std::string> alias_map;
 std::unordered_map<std::string, Field **> fields;
 // the table might be opened in engine_pushdown() for
 // pushdown join optimization - if so, when the
 // table is iterated over these pointers will be
 // used instead of opening the table again.  This
 // information is set during condition pushdown
 // and persisted on the table handle after it completes
 // and then the pointers are set to NULL
 ibis::mensa* base_table;
 ibis::table* filtered_table;
};

std::mutex pushdown_mtx;
std::unordered_map<THD*, warp_pushdown_information*> pd_info;

// used as a type of lock to provide consistent snapshots
// to deleted rows not visible to older transactions
// when a write lock is freed it is downgraded to a 
// visibility lock.  when a transaction closes, any
// locks HISTORY locks older than that transaction are
// also freed

// history locks are for read consistent views after
// rows are deleted.  they are freed when the 
// all the transactions older then them have
// been closed.  When an EX lock is freed it is
// downgraded to a LOCK_HISTORY lock if any
// changes were made to the row under the EX lock
#define LOCK_HISTORY -1

// if a lock acquisition results in a deadlock then
// LOCK_DEADLOCK is returned from create_lock()
#define LOCK_DEADLOCK -2

// select FOR UPDATE takes READ_EX locks which can
// be converted to a LOCK_EX without checking
// for deadlocks
#define WRITE_INTENTION -3

class warp_lock {
  public:
  // trx_id that holds this lock
  uint64_t holder;

  //trx_id that this lock is waiting on
  uint64_t waiting_on;

  //lock type:LOCK_EX, LOCK_SH, LOCK_HISTORY, LOCK_DEADLOCK
  int lock_type = 0;
};

// markers for the transaction logs
const char begin_marker     = 1;
const char insert_marker    = 2;
const char delete_marker    = 3;
const char commit_marker    = 4;
const char rollback_marker  = 5;
const char savepoint_marker = 6;
#define ROLLBACK_STATEMENT 0

  
//Holds the state of a WARP transaction.  Instantiated in ::external_lock
//or ::start_stmt
class warp_trx {
  public:
  // used to log inserts during an insertion.  If a statement rolls
  // back this is used to undo the insert statements
  FILE* log = NULL;
  std::string log_filename = "";
  bool registered = false;
  bool table_lock = false;
  
  // set when a statement is a DML statement
  // forces UPDATE and DELETE statements 
  // to be read-committed
  bool is_dml = false;

  // set when a SELECT has LOCK IN SHARE MODE as
  // part of the SELECT clause - takes shared locks
  // for each traversed visible row
  bool lock_in_share_mode = false;

  // when FOR UPDATE is in a SELECT clause
  // LOCK_EX is taken on traversed visible rows
  bool for_update = false;

  // held during commit and rollback
  std::mutex commit_mtx;
  
  //the transaction identifier 
  ulonglong trx_id = 0;

  //number of table locks (read or write) held by the transaction
  uint64_t lock_count = 0;

  //number of background writers that are doing work.  The commit
  //function must wait for this counter to reach zero before a 
  //transaction can be committed
  uint64_t background_writer_count = 0;

  THD* thd = NULL;
  handlerton* hton; 

  //the transaction was not a read-only transaction and it 
  //modified rows in the database, so it must be writen into
  //the commit bitmap when it commmits
  bool dirty = false;

  //autocommit statements commit each time the commit function
  //is called
  bool autocommit = false;

  //selected transaction isolation level.  Only SERIALIZABLE,
  //REPEATABLE-READ and READ-COMMITTED are actually supported
  enum enum_tx_isolation isolation_level;

  //called when transactions start
  int begin();
  
  //called when transcations end
  void commit();

  void rollback(bool all);
  void write_insert_log_rowid(uint64_t rowid);
  void write_delete_log_rowid(uint64_t rowid);
  void open_log();
};

class warp_global_data {
  private:
  // held when reading or modifying state
  std::mutex mtx;
  // used when reading/modifying the lock structures

  std::mutex lock_mtx;
  std::mutex history_lock_mtx;
  std::string shutdown_clean_file = "shutdown_clean.warp";
  std::string warp_state_file     = "state.warp";
  std::string commit_bitmap_file  = "commits.warp";
  std::string delete_bitmap_file  = "deletes.warp";

  uint64_t rowid_batch_size = 10000;

  // each write to the state file increments the state counter
  // the state file has two records.  the state record with
  // the highest counter is used.
  uint64_t state_counter = 1;
  
  // Each time a transaction is handed out, this is pre-incremented
  // and the value is used for the tranaction identifier.  When the
  // transaction is committed, this idenifier is written into the
  // commit bitmap once all the background writers associated with
  // the transaction complete writing.
  ulonglong next_trx_id = 1;

  // Each time a write into a table starts, WARP hands out 
  // a set of 10000 rowid values, and this counter is 
  // incremented by 10000.  If a transaction runs out of
  // rowid values, it can request another batch of 10000
  // more.  Since rowid values are 64 bit, handing out 
  // in 10000 row batches is fine.  This value is persisted
  // between database restarts.
  uint64_t next_rowid = 1;

  // in order to detect unique keys during insertions or updates
  // it is necessary to distinguish between a transaction that
  // was rolled back and thus is missing from the commit bitmap
  // because of rollback or crash, or a transaction that is 
  // currently open for write.  In the first case, the unique
  // check must ignore the row, but in the second case the 
  // unique check must fail, otherwise duplicate values could
  // end up in a column with a unique or primary key
  std::forward_list<uint64_t> open_write_trx;

  /* this is used to read/write on disk state */
  struct on_disk_state {
    public:
    uint64_t version;
    uint64_t next_trx_id;
    uint64_t next_rowid;
    uint64_t state_counter;
  };

  // handle to the warp state
  FILE* fp = NULL;

  //rowid, warp_lock object
  std::unordered_multimap<uint64_t, warp_lock> row_locks;
  
  // rowid, trx_id
  std::unordered_map<uint64_t, uint64_t> history_locks;

  // write the current state to the state file
  void write();

  // checks the state of the on-disk state
  bool check_state();

  // reads the state from disk
  uint64_t get_state_and_return_version();

  // return false if shutdown file was not found
  bool was_shutdown_clean();

  // used to repair tables
  bool repair_tables();

  void write_clean_shutdown();

  public:
  // bitmap into which committed transactions are persisted
  // sparse bitmaps have write-ahead logging so a crash 
  // during commit will result in the transaction never
  // becoming visible
  // note because the sparse bitmap implements locking
  // the mutex does not need to be held to modify 
  // the commit bitmap
  sparsebitmap* commit_bitmap = NULL;
  sparsebitmap* delete_bitmap = NULL;
  // opens and reads the state file.  
  // if the on-disk version of data is older than the current verion
  // the database will be upgraded.  If the on disk version is newer
  // than the current version, this will assert and the database will
  // fail to start and MySQL will be crashed on purpose!
  // if shutdown was not clean, then table repair will be executed.
  warp_global_data();

  // called at database shutdown.  
  // Calls write() to persist the state to disk
  // writes the clean shutdown file
  ~warp_global_data();
  
  uint64_t get_next_rowid_batch();
  uint64_t get_next_trx_id();
  bool is_transaction_open(uint64_t check_trx_id);
  void mark_transaction_closed(uint64_t trx_id);
  void register_open_trx(uint64_t trx);

  int create_lock(uint64_t lock_id, warp_trx* trx, int lock_type);
  int unlock(uint64_t rowid, warp_trx* trx);
  int downgrade_to_history_lock(uint64_t rowid, warp_trx* trx);
  int free_locks(warp_trx* trx);
  uint64_t get_history_lock(uint64_t rowid);

};

//Initialized in the SE init function, destroyed when engine is removed
warp_global_data* warp_state;

//The MySQL table share functions
static WARP_SHARE *get_share(const char *table_name, TABLE* table_ptr);
static int free_share(WARP_SHARE *share); 

//Called when a transaction or statement commits.  A pointer to this
//function is registered on the hanlderton
int warp_commit(handlerton*, THD *, bool);

//Called when a transaction or statement rolls back
// A pointer to this function is registered on the hanlderton                       
int warp_rollback(handlerton *, THD *, bool);

//Called by the warp_state constructor to upgrade on disk tables when
//the on-disk version is older than the current version
int warp_upgrade_tables(uint16_t version);

// determines is a transaction_id is an open transaction
// used for UNIQUE check visibility during inserts
// and for REPEATABLE READ during scans
bool warp_is_trx_open(uint64_t trx_id);

//warp_trx* warp_get_trx(handlerton* hton, THD* thd);

//This is the handler where the majority of the work is done.  Handles
//creating and dropping tables, TRUNCATE table, reading from indexes,
//scanning tables, inserts, updates, deletes, engine condition pushdown
class ha_warp : public handler {
  /* MySQL lock - Fastbit has its own internal mutex implementation.  This is used to protect the share.*/
  THR_LOCK_DATA lock; 

  /* Shared lock info */
  WARP_SHARE *share;  

 /* used in visibility checks */
 uint64_t last_trx_id = 0;
 bool is_visible = false;
 warp_trx* current_trx = NULL;


 private:
  void update_row_count();
  int reset_table();
  int encode_quote(uchar *buf);
  int set_column_set(); 
  int set_column_set(uint32_t idxno);
  int find_current_row(uchar *buf, ibis::table::cursor* cursor);
  void create_writer(TABLE *table_arg);
  static int get_writer_partno(ibis::tablex* writer, char* datadir);
  static void background_write(ibis::tablex* writer,  char* datadir, TABLE* table, WARP_SHARE* share);
  void foreground_write();
  bool append_column_filter(const Item* cond, std::string& push_where_clause); 
  static void maintain_indexes(char* datadir, TABLE* table);
  void open_deleted_bitmap(int lock_mode = LOCK_SH);
  void close_deleted_bitmap();
  bool is_deleted(uint64_t rowid);
  //void write_dirty_rows();
  int open_trx_log();
  int close_trx_log();
  std::string unique_check_where_clause = "";
  bool table_checked_unique_keys = false;
  bool table_has_unique_keys = false;
  String key_part_tmp;
  String key_part_esc;
  bool has_unique_keys();
  void make_unique_check_clause();

  warp_pushdown_information* pushdown_info = NULL;
  bool table_opened_in_pushdown = false;

  //std::mutex thd_lock;

  /* These objects are used to access the FastBit tables for tuple reads.*/ 
  ibis::mensa*         base_table         = NULL; 
  ibis::table*         filtered_table     = NULL;
  ibis::table*         idx_filtered_table = NULL;
  ibis::table::cursor* cursor             = NULL;
  ibis::table::cursor* idx_cursor         = NULL;

  /* These objects are used by WARP to add functionality to Fastbit
     such as deletion/update of rows and transactions
  */
  sparsebitmap*        deleted_bitmap     = NULL;  
  sparsebitmap*        commit_bitmap      = NULL;    
  FILE*                insert_log         = NULL; 

  /* WHERE clause constructed from engine condition pushdown */
  std::string          push_where_clause  = "";

  /* This object is used to append tuples to the table */
  ibis::tablex* writer = NULL;

  /* A list of row numbers to delete (filled in by delete_row) */
  std::vector<uint64_t> deleted_rows;

  /* this is always the rowid of the current row */
  uint64_t current_rowid = 0;  

  /* a SELECT lists of the columns that have been fetched for the current query */
  std::string column_set = "";
  std::string index_column_set = "";

  /* temporary buffer populated with CSV of row for insertions*/
  String buffer;

  /* storage for BLOBS */
  MEM_ROOT blobroot; 

  /* set to true if the table has deleted rows */
  bool has_deleted_rows = false;

 public:
  ha_warp(handlerton *hton, TABLE_SHARE *table_arg);
  handlerton* warp_hton;
  ~ha_warp() {
    //free_root(&blobroot, MYF(0));
  }
 
  const char *table_type() const { return "WARP"; }
 
  ulonglong table_flags() const {
    // return (HA_NO_TRANSACTIONS | HA_NO_AUTO_INCREMENT | HA_BINLOG_ROW_CAPABLE | HA_CAN_REPAIR);
    return (HA_BINLOG_ROW_CAPABLE | HA_CAN_REPAIR);
  }
 
  uint max_record_length() const { return HA_MAX_REC_LENGTH; }
  uint max_keys() const { return 16384; }
  uint max_key_parts() const { return 1; }
  uint max_key_length() const { return HA_MAX_REC_LENGTH; }
  uint max_supported_keys() const { return 16384; }
  uint max_supported_key_length() const { return 1024; }
  uint max_supported_key_part_length(
      HA_CREATE_INFO *create_info MY_ATTRIBUTE((unused))) const {
    return 1024;
  }

  /*
     Called in test_quick_select to determine if indexes should be used.
   */
  virtual double scan_time() {
    //return (double)(stats.records + stats.deleted) / 20.0 + 10;
    return 1.0/(stats.records > 0 ? stats.records : 1);
  }

  /* The next method will never be called */
  virtual bool fast_key_read() { return 1; }
  ha_rows estimate_rows_upper_bound() { return HA_POS_ERROR; }

  int open(const char *name, int mode, uint open_options,
           const dd::Table *table_def);
  int close(void);

  
  const char **bas_ext() const ;
  int write_row(uchar *buf);
  int update_row(const uchar *old_data, uchar *new_data);
  int delete_row(const uchar *buf);
  int rnd_init(bool scan = 1);
  int rnd_next(uchar *buf);
  int rnd_pos(uchar *buf, uchar *pos);
  bool check_and_repair(THD *thd);
  int check(THD *thd, HA_CHECK_OPT *check_opt);
  bool is_crashed() const;
  int rnd_end();
  int repair(THD *thd, HA_CHECK_OPT *check_opt);
  /* This is required for SQL layer to know that we support autorepair */
  bool auto_repair() const { return 1; }
  void position(const uchar *record);
  int info(uint);
  int extra(enum ha_extra_function operation);
  int delete_all_rows(void);
  int create(const char *name, TABLE *form, HA_CREATE_INFO *create_info,
             dd::Table *table_def);
  bool check_if_incompatible_data(HA_CREATE_INFO *info, uint table_changes);
  int delete_table(const char *table_name, const dd::Table *);
  int get_or_create_trx(THD* thd, warp_trx* &trx);
  int external_lock(THD *thd, int lock_type);
  int start_stmt(THD *thd, thr_lock_type lock_type);
  int register_trx_with_mysql(THD* thd, warp_trx* trx);
  bool is_trx_visible_to_read(uint64_t row_trx_id);
  bool is_row_visible_to_read(uint64_t rowid);
  
  //int truncate(dd::Table *);
  THR_LOCK_DATA **store_lock(THD *thd, THR_LOCK_DATA **to,
                             enum thr_lock_type lock_type);

  /*
    These functions used to get/update status of the handler.
    Needed to enable concurrent inserts.
  */
  void get_status();
  void update_status();

  // Functions to support indexing
  ulong index_flags(uint, uint, bool) const;
  ha_rows records_in_range(uint idxno, key_range *, key_range *); 
  int index_init(uint idxno, bool sorted);
  int index_init(uint idxno);
  int index_next(uchar * buf);
  int index_first(uchar * buf);
  int index_end();
  int index_read_map (uchar *buf, const uchar *key, key_part_map keypart_map, enum ha_rkey_function find_flag);
  int index_read_idx_map (uchar *buf, uint idxno, const uchar *key, key_part_map keypart_map, enum ha_rkey_function find_flag);
  int make_where_clause(const uchar *key, key_part_map keypart_map, enum ha_rkey_function find_flag, std::string& where_clause);
  void get_auto_increment	(	
    ulonglong 	offset,
    ulonglong 	increment,
    ulonglong 	nb_desired_values,
    ulonglong * 	first_value,
    ulonglong * 	nb_reserved_values 
  );

  // Functions to support engine condition pushdown (ECP)
  int engine_push(AQP::Table_access *table_aqp);
  const Item* cond_push(const Item *cond,	bool other_tbls_ok );
	
  int rename_table(const char * from, const char * to, const dd::Table* , dd::Table* );
  
};
#endif
