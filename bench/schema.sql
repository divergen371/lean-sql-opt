DROP TABLE IF EXISTS store_sales;
DROP TABLE IF EXISTS date_dim;
DROP TABLE IF EXISTS item;
DROP TABLE IF EXISTS customer;
DROP TABLE IF EXISTS store;
DROP TABLE IF EXISTS promotion;

CREATE TABLE date_dim (
    d_date_sk INTEGER PRIMARY KEY,
    d_year    INTEGER,
    d_moy     INTEGER,
    d_qoy     INTEGER
);

CREATE TABLE item (
    i_item_sk  INTEGER PRIMARY KEY,
    i_brand_id INTEGER,
    i_category VARCHAR(50),
    i_class    VARCHAR(50)
);

CREATE TABLE customer (
    c_customer_sk INTEGER PRIMARY KEY,
    c_birth_year  INTEGER,
    c_customer_id VARCHAR(32)
);

CREATE TABLE store (
    s_store_sk INTEGER PRIMARY KEY,
    s_state    VARCHAR(10),
    s_city     VARCHAR(50)
);

CREATE TABLE promotion (
    p_promo_sk      INTEGER PRIMARY KEY,
    p_channel_email VARCHAR(1),
    p_channel_dmail VARCHAR(1)
);

CREATE TABLE store_sales (
    ss_sold_date_sk    INTEGER NOT NULL REFERENCES date_dim(d_date_sk),
    ss_item_sk         INTEGER NOT NULL REFERENCES item(i_item_sk),
    ss_customer_sk     INTEGER NOT NULL REFERENCES customer(c_customer_sk),
    ss_store_sk        INTEGER NOT NULL REFERENCES store(s_store_sk),
    ss_promo_sk        INTEGER NOT NULL REFERENCES promotion(p_promo_sk),
    ss_ticket_number   BIGINT NOT NULL,
    ss_quantity        INTEGER,
    ss_sales_price     BIGINT,
    ss_ext_sales_price BIGINT,
    ss_net_paid        BIGINT
);
