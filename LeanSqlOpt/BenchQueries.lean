import LeanSqlOpt.SqlPrint

namespace LeanSqlOpt

def tpcdsSchema : Schema where
  tableCols
    | "store_sales" =>
      [ "ss_sold_date_sk", "ss_item_sk", "ss_customer_sk", "ss_store_sk",
        "ss_promo_sk", "ss_ticket_number", "ss_quantity", "ss_sales_price",
        "ss_ext_sales_price", "ss_net_paid" ]
    | "date_dim" => ["d_date_sk", "d_year", "d_moy", "d_qoy"]
    | "item" => ["i_item_sk", "i_brand_id", "i_category", "i_class"]
    | "customer" => ["c_customer_sk", "c_birth_year", "c_customer_id"]
    | "store" => ["s_store_sk", "s_state", "s_city"]
    | "promotion" => ["p_promo_sk", "p_channel_email", "p_channel_dmail"]
    | _ => []
  notNull
    | "store_sales", "ss_sold_date_sk" => true
    | "store_sales", "ss_item_sk" => true
    | "store_sales", "ss_customer_sk" => true
    | "store_sales", "ss_store_sk" => true
    | "store_sales", "ss_promo_sk" => true
    | "date_dim", "d_date_sk" => true
    | "item", "i_item_sk" => true
    | "customer", "c_customer_sk" => true
    | "store", "s_store_sk" => true
    | "promotion", "p_promo_sk" => true
    | _, _ => false
  uniqueKey
    | "date_dim", "d_date_sk" => true
    | "item", "i_item_sk" => true
    | "customer", "c_customer_sk" => true
    | "store", "s_store_sk" => true
    | "promotion", "p_promo_sk" => true
    | _, _ => false
  foreignKeys :=
    [ ⟨"store_sales", "ss_sold_date_sk", "date_dim", "d_date_sk"⟩
    , ⟨"store_sales", "ss_item_sk", "item", "i_item_sk"⟩
    , ⟨"store_sales", "ss_customer_sk", "customer", "c_customer_sk"⟩
    , ⟨"store_sales", "ss_store_sk", "store", "s_store_sk"⟩
    , ⟨"store_sales", "ss_promo_sk", "promotion", "p_promo_sk"⟩
    ]

private def scanSS (alias : String := "ss") : Query :=
  .scan "store_sales" alias (tpcdsSchema.tableCols "store_sales")

private def scanDate (alias : String := "d") : Query :=
  .scan "date_dim" alias (tpcdsSchema.tableCols "date_dim")

private def scanItem (alias : String := "i") : Query :=
  .scan "item" alias (tpcdsSchema.tableCols "item")

private def scanCustomer (alias : String := "c") : Query :=
  .scan "customer" alias (tpcdsSchema.tableCols "customer")

private def scanStore (alias : String := "s") : Query :=
  .scan "store" alias (tpcdsSchema.tableCols "store")

private def scanPromo (alias : String := "p") : Query :=
  .scan "promotion" alias (tpcdsSchema.tableCols "promotion")

structure BenchQuery where
  id : String
  title : String
  query : Query

/-- Q1: Eager Aggregation (TPC-DS 年別売上集計) -/
def benchQ1 : BenchQuery where
  id := "Q1_eager_agg_date"
  title := "年別売上集計 (Eager Aggregation + Filter Pushdown)"
  query :=
    .groupBy
      ["d__d_year"]
      [ ⟨.sumCol "ss__ss_ext_sales_price", "sum_sales"⟩
      , ⟨.sumCol "ss__ss_net_paid", "sum_net"⟩
      , ⟨.countStar, "cnt"⟩
      ]
      (.filter
        (.gt (.col "d__d_year") (.lit (.int 2019)))
        (.innerJoin (scanSS "ss") (scanDate "d")
          (.eq (.col "ss__ss_sold_date_sk") (.col "d__d_date_sk"))))

/-- Q2: Eager Aggregation (カテゴリ別売上集計) -/
def benchQ2 : BenchQuery where
  id := "Q2_eager_agg_item"
  title := "商品カテゴリ別売上集計 (Eager Aggregation)"
  query :=
    .groupBy
      ["i__i_category"]
      [ ⟨.sumCol "ss__ss_ext_sales_price", "sum_sales"⟩
      , ⟨.sumCol "ss__ss_quantity", "sum_qty"⟩
      , ⟨.maxCol "ss__ss_net_paid", "max_paid"⟩
      , ⟨.countStar, "cnt"⟩
      ]
      (.innerJoin (scanSS "ss") (scanItem "i")
        (.eq (.col "ss__ss_item_sk") (.col "i__i_item_sk")))

/-- Q3: 冗長 FK JOIN 除去 (不要な customer / promotion 結合を含む売上集計) -/
def benchQ3 : BenchQuery where
  id := "Q3_redundant_fk_join"
  title := "冗長な外部キー結合の除去 (customer + promotion 削除)"
  query :=
    .groupBy
      ["ss__ss_store_sk"]
      [ ⟨.sumCol "ss__ss_net_paid", "total_paid"⟩
      , ⟨.countStar, "tx_cnt"⟩
      ]
      (.project
        [ ⟨.col "ss__ss_store_sk", "ss__ss_store_sk"⟩
        , ⟨.col "ss__ss_net_paid", "ss__ss_net_paid"⟩
        ]
        (.innerJoin
          (.innerJoin (scanSS "ss") (scanCustomer "c")
            (.eq (.col "ss__ss_customer_sk") (.col "c__c_customer_sk")))
          (scanPromo "p")
          (.eq (.col "ss__ss_promo_sk") (.col "p__p_promo_sk"))))

/-- Q4: クロス結合 OR -> UNION ALL 分割 (別テーブル条件 OR のインデックス駆動化) -/
def benchQ4 : BenchQuery where
  id := "Q4_or_to_union_all"
  title := "結合を跨ぐ OR 条件の 3値論理対応 UNION ALL 分割"
  query :=
    .project
      [ ⟨.col "ss__ss_ticket_number", "ticket"⟩
      , ⟨.col "ss__ss_net_paid", "net_paid"⟩
      , ⟨.col "d__d_date_sk", "date_sk"⟩
      , ⟨.col "i__i_item_sk", "item_sk"⟩
      ]
      (.filter
        (.or
          (.eq (.col "d__d_date_sk") (.lit (.int 1500)))
          (.eq (.col "i__i_brand_id") (.lit (.int 77))))
        (.innerJoin
          (.innerJoin (scanSS "ss") (scanDate "d")
            (.eq (.col "ss__ss_sold_date_sk") (.col "d__d_date_sk")))
          (scanItem "i")
          (.eq (.col "ss__ss_item_sk") (.col "i__i_item_sk"))))

/-- Q5: 相関スカラー集約サブクエリのデコレレーション (TPC-DS Q1 型: 店舗平均超過取引) -/
def benchQ5 : BenchQuery where
  id := "Q5_decorrelate_subq"
  title := "店舗平均を上回る明細の抽出・集計 (相関サブクエリの JOIN 化)"
  query :=
    .groupBy
      ["ss1__ss_store_sk"]
      [ ⟨.sumCol "ss1__ss_net_paid", "high_paid_sum"⟩
      , ⟨.countStar, "high_cnt"⟩
      ]
      (.corrAggFilter
        (scanSS "ss1")
        "ss1__ss_net_paid"
        .gt
        (scanSS "ss2")
        "ss1__ss_store_sk"
        "ss2__ss_store_sk"
        (.avgCol "ss2__ss_net_paid"))

/-- Q6: ベースライン通常クエリ (基本ルールのみ適用される比較クエリ) -/
def benchQ6 : BenchQuery where
  id := "Q6_base_only"
  title := "基本フィルタプッシュダウンのみ適用される標準集計クエリ"
  query :=
    .groupBy
      ["s__s_state"]
      [ ⟨.avgCol "ss__ss_net_paid", "avg_paid"⟩
      , ⟨.countStar, "cnt"⟩
      ]
      (.filter
        (.gt (.col "ss__ss_quantity") (.lit (.int 5)))
        (.filter
          (.eq (.col "s__s_state") (.lit (.str "TX")))
          (.innerJoin (scanSS "ss") (scanStore "s")
            (.eq (.col "ss__ss_store_sk") (.col "s__s_store_sk")))))

def allBenchQueries : List BenchQuery :=
  [benchQ1, benchQ2, benchQ3, benchQ4, benchQ5, benchQ6]

end LeanSqlOpt
