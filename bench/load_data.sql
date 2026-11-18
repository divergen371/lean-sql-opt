TRUNCATE TABLE store_sales, date_dim, item, customer, store, promotion;

INSERT INTO date_dim (d_date_sk, d_year, d_moy, d_qoy)
SELECT
    g AS d_date_sk,
    CASE WHEN g <> 1500 AND g % 50 = 0 THEN NULL ELSE 2015 + ((g - 1) / 365) END AS d_year,
    1 + (((g - 1) % 365) / 31) AS d_moy,
    1 + (((g - 1) % 365) / 92) AS d_qoy
FROM generate_series(1, 3650) AS g;

INSERT INTO item (i_item_sk, i_brand_id, i_category, i_class)
SELECT
    g AS i_item_sk,
    CASE WHEN g % 40 = 0 THEN NULL ELSE 1 + ((g * 17) % 250) END AS i_brand_id,
    (ARRAY['Books', 'Electronics', 'Home', 'Music', 'Sports', 'Shoes', 'Men', 'Women', 'Children', 'Jewelry'])[1 + (g % 10)] AS i_category,
    'class_' || (g % 25)::text AS i_class
FROM generate_series(1, 20000) AS g;

INSERT INTO customer (c_customer_sk, c_birth_year, c_customer_id)
SELECT
    g AS c_customer_sk,
    1945 + (g % 60) AS c_birth_year,
    'CUST_' || lpad(g::text, 8, '0') AS c_customer_id
FROM generate_series(1, 50000) AS g;

INSERT INTO store (s_store_sk, s_state, s_city)
SELECT
    g AS s_store_sk,
    CASE
        WHEN g % 37 = 0 THEN NULL
        ELSE (ARRAY['TX', 'CA', 'NY', 'FL', 'WA', 'IL', 'OH', 'GA', 'NC', 'MI',
                    'AZ', 'MA', 'VA', 'CO', 'TN', 'IN', 'MO', 'WI', 'MN', 'OR'])[1 + (g % 20)]
    END AS s_state,
    'city_' || (g % 40)::text AS s_city
FROM generate_series(1, 200) AS g;

INSERT INTO promotion (p_promo_sk, p_channel_email, p_channel_dmail)
SELECT
    g AS p_promo_sk,
    CASE WHEN g % 2 = 0 THEN 'Y' ELSE 'N' END,
    CASE WHEN g % 3 = 0 THEN 'Y' ELSE 'N' END
FROM generate_series(1, 500) AS g;

INSERT INTO store_sales (
    ss_sold_date_sk,
    ss_item_sk,
    ss_customer_sk,
    ss_store_sk,
    ss_promo_sk,
    ss_ticket_number,
    ss_quantity,
    ss_sales_price,
    ss_ext_sales_price,
    ss_net_paid
)
SELECT
    1 + ((g * 2654435761::bigint) % 3650)::int AS ss_sold_date_sk,
    1 + ((g * 1140071481::bigint) % 20000)::int AS ss_item_sk,
    1 + ((g * 40503::bigint) % 50000)::int AS ss_customer_sk,
    1 + ((g * 97::bigint) % 200)::int AS ss_store_sk,
    1 + ((g * 53::bigint) % 500)::int AS ss_promo_sk,
    g::bigint AS ss_ticket_number,
    CASE WHEN g % 50 = 0 THEN NULL ELSE 1 + (g % 12) END AS ss_quantity,
    10 + (g % 90) AS ss_sales_price,
    CASE WHEN g % 60 = 0 THEN NULL ELSE (1 + (g % 12))::bigint * (10 + (g % 90))::bigint END AS ss_ext_sales_price,
    CASE WHEN g % 45 = 0 THEN NULL ELSE (1 + (g % 12))::bigint * (8 + (g % 85))::bigint END AS ss_net_paid
FROM generate_series(1, 2000000) AS g;

CREATE INDEX idx_ss_date_sk ON store_sales(ss_sold_date_sk);
CREATE INDEX idx_ss_item_sk ON store_sales(ss_item_sk);
CREATE INDEX idx_ss_store_sk ON store_sales(ss_store_sk);
CREATE INDEX idx_item_brand_id ON item(i_brand_id);
CREATE INDEX idx_date_year ON date_dim(d_year);
CREATE INDEX idx_store_state ON store(s_state);

VACUUM ANALYZE;
