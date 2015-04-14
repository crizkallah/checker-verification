theory Check_Shortest_Path_Impl
imports
  "Vcg"
  "../Witness_Property/Shortest_Path_Theory"
"~~/src/HOL/Statespace/StateSpaceLocale"
begin

type_synonym IVertex = nat
type_synonym IEdge_Id = nat
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym ICost = "IEdge_Id \<Rightarrow> nat"
type_synonym IDist = "IVertex \<Rightarrow> ereal"
type_synonym IPEdge = "IVertex \<Rightarrow> IEdge_Id option"
type_synonym INum = "IVertex \<Rightarrow> enat"
type_synonym IGraph = "nat \<times> nat \<times> (IEdge_Id \<Rightarrow> IEdge)" 

abbreviation ivertex_cnt :: "IGraph \<Rightarrow> nat"
  where "ivertex_cnt G \<equiv> fst G"

abbreviation iedge_cnt :: "IGraph \<Rightarrow> nat"
  where "iedge_cnt G \<equiv> fst (snd G)"

abbreviation iarcs :: "IGraph \<Rightarrow> IEdge_Id \<Rightarrow> IEdge"
  where "iarcs G \<equiv> snd (snd G)"

definition is_wellformed_inv :: "IGraph \<Rightarrow> nat \<Rightarrow> bool" where
  "is_wellformed_inv G i \<equiv> \<forall>k < i. ivertex_cnt G > fst (iarcs G k)
        \<and> ivertex_cnt G > snd (iarcs G k)"

procedures is_wellformed (G :: IGraph | R :: bool)
  where
    i :: nat
    e :: IEdge
  in "
    ANNO G.
      \<lbrace> \<acute>G = G \<rbrace>
      \<acute>R :== True ;;
      \<acute>i :== 0 ;;
      TRY
        WHILE \<acute>i < iedge_cnt \<acute>G
        INV \<lbrace> \<acute>R = is_wellformed_inv \<acute>G \<acute>i \<and> \<acute>i \<le> iedge_cnt \<acute>G \<and> \<acute>G = G \<rbrace>
        VAR MEASURE (iedge_cnt \<acute>G - \<acute>i)
        DO
         \<acute>e :== iarcs \<acute>G \<acute>i ;;
         IF ivertex_cnt \<acute>G \<le> fst \<acute>e \<or> ivertex_cnt \<acute>G \<le> snd \<acute>e THEN
           \<acute>R :== False ;;
           THROW
         FI ;;
         \<acute>i :== \<acute>i + 1
        OD
      CATCH SKIP END
      \<lbrace> \<acute>G = G \<and> \<acute>R = is_wellformed_inv \<acute>G (iedge_cnt \<acute>G) \<rbrace>
    "

definition trian_inv :: "IGraph \<Rightarrow> IDist \<Rightarrow> ICost \<Rightarrow> nat \<Rightarrow> bool" where
  "trian_inv G d c m \<equiv> 
    \<forall>i < m. d (snd (iarcs G i)) \<le> d (fst (iarcs G i)) + ereal (c i)"

procedures trian (G :: IGraph, dist :: IDist, c :: ICost | R :: bool)
  where
    edge_id :: IEdge_Id
  in "
    ANNO (G,dist,c).
      \<lbrace> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>c = c \<rbrace>
      \<acute>R :== True ;;
      \<acute>edge_id :== 0 ;;
      TRY
        WHILE \<acute>edge_id < iedge_cnt \<acute>G
        INV \<lbrace> \<acute>R = trian_inv \<acute>G \<acute>dist \<acute>c \<acute>edge_id
          \<and> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>c = c
          \<and> \<acute>edge_id \<le> iedge_cnt \<acute>G\<rbrace>
        VAR MEASURE (iedge_cnt \<acute>G - \<acute>edge_id)
        DO
          IF  \<acute>dist (snd (iarcs \<acute>G \<acute>edge_id)) > 
              \<acute>dist (fst (iarcs \<acute>G \<acute>edge_id)) + 
              ereal (\<acute>c \<acute>edge_id) THEN
            \<acute>R :== False ;;
            THROW
          FI ;;
          \<acute>edge_id :== \<acute>edge_id + 1
        OD
      CATCH SKIP END
      \<lbrace> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>c = c
      \<and> \<acute>R = trian_inv \<acute>G \<acute>dist \<acute>c (iedge_cnt \<acute>G) \<rbrace>
    "

definition just_inv :: 
  "IGraph \<Rightarrow> IDist \<Rightarrow> ICost \<Rightarrow> IVertex \<Rightarrow> INum \<Rightarrow> IPEdge \<Rightarrow> nat \<Rightarrow> bool" where
  "just_inv G d c s n p k \<equiv> 
    \<forall>v < k. v \<noteq> s \<and> n v \<noteq> \<infinity> \<longrightarrow> 
      (\<exists> e. e = the (p v) \<and> e < iedge_cnt G \<and> 
        v = snd (iarcs G e) \<and>
        d v = d (fst (iarcs G e)) + ereal (c e) \<and>
        n v = n (fst (iarcs G e)) + (enat 1))"

procedures just (G :: IGraph, dist :: IDist, c :: ICost, 
    s :: IVertex, enum :: INum, pred :: IPEdge | R :: bool)
  where
    v :: IVertex
    edge_id :: IEdge_Id
  in "
    ANNO (G,dist, c, s ,enum, pred).
      \<lbrace> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = enum \<and> \<acute>pred = pred\<rbrace>
      \<acute>R :== True ;;
      \<acute>v :== 0 ;;
      TRY
        WHILE \<acute>v < ivertex_cnt \<acute>G
        INV \<lbrace> \<acute>R = just_inv \<acute>G \<acute>dist \<acute>c \<acute>s \<acute>enum \<acute>pred \<acute>v
          \<and> \<acute>G = G \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>dist = dist 
          \<and> \<acute>enum = enum \<and> \<acute>pred = pred
          \<and> \<acute>v \<le> ivertex_cnt \<acute>G\<rbrace>
        VAR MEASURE (ivertex_cnt \<acute>G - \<acute>v)
        DO
          \<acute>edge_id :== the (\<acute>pred \<acute>v) ;;
          IF (\<acute>v \<noteq> \<acute>s) \<and>  \<acute>enum \<acute>v \<noteq> \<infinity> \<and>
             (\<acute>edge_id \<ge> iedge_cnt \<acute>G 
              \<or> snd (iarcs \<acute>G \<acute>edge_id) \<noteq> \<acute>v
              \<or> \<acute>dist \<acute>v \<noteq> 
                \<acute>dist (fst (iarcs \<acute>G \<acute>edge_id)) + ereal (\<acute>c \<acute>edge_id)
              \<or> \<acute>enum \<acute>v \<noteq> \<acute>enum (fst (iarcs \<acute>G \<acute>edge_id)) + (enat 1)) THEN
            \<acute>R :== False ;;
            THROW
          FI;;
          \<acute>v :== \<acute>v + 1
        OD
      CATCH SKIP END
    \<lbrace> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>c = c \<and> \<acute>s = s \<and> \<acute>enum = enum \<and> \<acute>pred = pred
      \<and> \<acute>R = just_inv \<acute>G \<acute>dist \<acute>c \<acute>s \<acute>enum \<acute>pred (ivertex_cnt \<acute>G) \<rbrace>
  "

definition no_path_inv :: "IGraph \<Rightarrow> IDist \<Rightarrow> INum \<Rightarrow> nat \<Rightarrow> bool" where
  "no_path_inv G d n k \<equiv>  \<forall>v < k. (d v = \<infinity> \<longleftrightarrow> n v = \<infinity>)"

procedures no_path (G :: IGraph, dist :: IDist, enum :: INum | R :: bool)
  where
    v :: IVertex
  in "
    ANNO (G,dist,enum).
      \<lbrace> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>enum = enum \<rbrace>
      \<acute>R :== True ;;
      \<acute>v :== 0 ;;
      TRY
        WHILE \<acute>v < ivertex_cnt \<acute>G
        INV \<lbrace> \<acute>R = no_path_inv \<acute>G \<acute>dist \<acute>enum \<acute>v
          \<and> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>enum = enum
          \<and> \<acute>v \<le> ivertex_cnt \<acute>G\<rbrace>
        VAR MEASURE (ivertex_cnt \<acute>G - \<acute>v)
        DO
          IF  \<not>(\<acute>dist \<acute>v = \<infinity> \<longleftrightarrow> \<acute>enum \<acute>v = \<infinity>) THEN
            \<acute>R :== False ;;
            THROW
          FI ;;
          \<acute>v :== \<acute>v + 1
        OD
      CATCH SKIP END
      \<lbrace> \<acute>G = G \<and> \<acute>dist = dist \<and> \<acute>enum = enum
      \<and> \<acute>R = no_path_inv \<acute>G \<acute>dist \<acute>enum (ivertex_cnt \<acute>G) \<rbrace>
    "

definition non_neg_cost_inv :: "IGraph \<Rightarrow> ICost \<Rightarrow> nat \<Rightarrow> bool" where
  "non_neg_cost_inv G c m \<equiv>  \<forall>e < m. c e \<ge> 0"

procedures non_neg_cost (G :: IGraph, c :: ICost | R :: bool)
  where
    edge_id :: IEdge_Id
  in "
    ANNO (G,c).
      \<lbrace> \<acute>G = G \<and> \<acute>c = c \<rbrace>
      \<acute>R :== True ;;
      \<acute>edge_id :== 0 ;;
      TRY
        WHILE \<acute>edge_id < iedge_cnt \<acute>G
        INV \<lbrace> \<acute>R = non_neg_cost_inv \<acute>G \<acute>c \<acute>edge_id
          \<and> \<acute>G = G \<and> \<acute>c = c
          \<and> \<acute>edge_id \<le> iedge_cnt \<acute>G\<rbrace>
        VAR MEASURE (iedge_cnt \<acute>G - \<acute>edge_id)
        DO
          IF \<acute>c \<acute>edge_id < 0 THEN
            \<acute>R :== False ;;
            THROW
          FI ;;
          \<acute>edge_id :== \<acute>edge_id + 1
        OD
      CATCH SKIP END
      \<lbrace> \<acute>G = G \<and> \<acute>c = c
      \<and> \<acute>R = non_neg_cost_inv \<acute>G \<acute>c (iedge_cnt \<acute>G) \<rbrace>
    "

procedures check_basic_just_sp (G :: IGraph, dist :: IDist, c :: ICost, 
    s :: IVertex, enum :: INum, pred :: IPEdge | R :: bool)
  where
    R1 :: bool
    R2 :: bool
    R3 :: bool
    R4 :: bool
  in "
    \<acute>R1 :== CALL is_wellformed (\<acute>G) ;;
    \<acute>R2 :== \<acute>dist \<acute>s \<le> 0 ;;
    \<acute>R3 :== CALL trian (\<acute>G, \<acute>dist, \<acute>c) ;;
    \<acute>R4 :== CALL just (\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred) ;;
    \<acute>R :== \<acute>R1 \<and> \<acute>R2 \<and> \<acute>R3 \<and> \<acute>R4
  "

procedures check_sp (G :: IGraph, dist :: IDist, c :: ICost, 
    s :: IVertex, enum :: INum, pred :: IPEdge | R :: bool)
  where
    R1 :: bool
    R2 :: bool
    R3 :: bool
    R4 :: bool
  in "
    \<acute>R1 :== CALL check_basic_just_sp (\<acute>G, \<acute>dist, \<acute>c, \<acute>s, \<acute>enum, \<acute>pred) ;;
    \<acute>R2 :== \<acute>s < ivertex_cnt \<acute>G \<and> \<acute>dist \<acute>s = 0 ;;
    \<acute>R3 :== CALL no_path (\<acute>G, \<acute>dist, \<acute>enum) ;;
    \<acute>R4 :== CALL non_neg_cost (\<acute>G, \<acute>c) ;;
    \<acute>R :== \<acute>R1 \<and> \<acute>R2 \<and> \<acute>R3 \<and> \<acute>R4
  "

end
