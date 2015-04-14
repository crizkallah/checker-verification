theory Check_Connected_Impl
imports
  "Vcg"
  "../Witness_Property/Connected_Components"
begin

type_synonym IVertex = nat
type_synonym IEdge_Id = nat
type_synonym IEdge = "IVertex \<times> IVertex"
type_synonym IPEdge = "IVertex \<Rightarrow> IEdge_Id option"
type_synonym INum = "IVertex \<Rightarrow> nat"
type_synonym IGraph = "nat \<times> nat \<times> (IEdge_Id \<Rightarrow> IEdge)" 

abbreviation ivertex_cnt :: "IGraph \<Rightarrow> nat"
  where "ivertex_cnt G \<equiv> fst G"

abbreviation iedge_cnt :: "IGraph \<Rightarrow> nat"
  where "iedge_cnt G \<equiv> fst (snd G)"

abbreviation iedges :: "IGraph \<Rightarrow> IEdge_Id \<Rightarrow> IEdge"
  where "iedges G \<equiv> snd (snd G)"

definition is_wellformed_inv :: "IGraph \<Rightarrow> nat \<Rightarrow> bool" where
  "is_wellformed_inv G i \<equiv> \<forall>k < i. ivertex_cnt G > fst (iedges G k)
        \<and> ivertex_cnt G > snd (iedges G k)"
ML {* Toplevel.theory *}
procedures is_wellformed (G :: IGraph | R :: bool)
  where
    i :: nat
    e :: IEdge
  in "
    ANNO G.\<lbrace> \<acute>G = G \<rbrace>
      \<acute>R :== True ;;
      \<acute>i :== 0 ;;
      TRY
        WHILE \<acute>i < iedge_cnt \<acute>G
        INV \<lbrace> \<acute>R = is_wellformed_inv \<acute>G \<acute>i \<and> 
              \<acute>i \<le> iedge_cnt \<acute>G \<and> \<acute>G = G \<rbrace>
        VAR MEASURE (iedge_cnt \<acute>G - \<acute>i)
        DO
         \<acute>e :== iedges \<acute>G \<acute>i ;;
         IF ivertex_cnt \<acute>G \<le> fst \<acute>e \<or> ivertex_cnt \<acute>G \<le> snd \<acute>e THEN
           \<acute>R :== False ;;
           THROW
         FI ;;
         \<acute>i :== \<acute>i + 1
        OD
      CATCH SKIP END
      \<lbrace> \<acute>G = G \<and> 
        \<acute>R = is_wellformed_inv \<acute>G (iedge_cnt \<acute>G) \<rbrace>"

definition parent_num_assms_inv :: "IGraph \<Rightarrow> IVertex \<Rightarrow> IPEdge \<Rightarrow> INum \<Rightarrow> nat \<Rightarrow> bool" where
  "parent_num_assms_inv G r p n k \<equiv> \<forall>i < k. i \<noteq> r \<longrightarrow> (case p i of
      None \<Rightarrow> False
    | Some x \<Rightarrow> x < iedge_cnt G \<and> snd (iedges G x) = i \<and> n i = n (fst (iedges G x)) + 1)"

procedures parent_num_assms (G :: IGraph, r :: IVertex, parent_edge :: IPEdge,
    num :: INum | R :: bool)
  where
    vertex :: IVertex
    edge_id :: IEdge_Id
  in "
    ANNO (G,r,p,n).
      \<lbrace> \<acute>G = G \<and> \<acute>r = r \<and> \<acute>parent_edge = p \<and> \<acute>num = n \<rbrace>
      \<acute>R :== True ;;
      \<acute>vertex :== 0 ;;
      TRY
        WHILE \<acute>vertex < ivertex_cnt \<acute>G
        INV \<lbrace> \<acute>R = parent_num_assms_inv \<acute>G \<acute>r \<acute>parent_edge \<acute>num \<acute>vertex
          \<and> \<acute>G = G \<and> \<acute>r = r \<and> \<acute>parent_edge = p \<and> \<acute>num = n
          \<and> \<acute>vertex \<le> ivertex_cnt \<acute>G\<rbrace>
        VAR MEASURE (ivertex_cnt \<acute>G - \<acute>vertex)
        DO
          IF (\<acute>vertex \<noteq> \<acute>r) THEN
            IF \<acute>parent_edge \<acute>vertex = None THEN
              \<acute>R :== False ;;
              THROW
            FI ;;
            \<acute>edge_id :== the (\<acute>parent_edge \<acute>vertex) ;;
            IF \<acute>edge_id \<ge> iedge_cnt \<acute>G
                \<or> snd (iedges \<acute>G \<acute>edge_id) \<noteq> \<acute>vertex
                \<or> \<acute>num \<acute>vertex \<noteq> \<acute>num (fst (iedges \<acute>G \<acute>edge_id)) + 1 THEN
              \<acute>R :== False ;;
              THROW
            FI
          FI ;;
          \<acute>vertex :== \<acute>vertex + 1
        OD
      CATCH SKIP END
    \<lbrace> \<acute>G = G \<and> \<acute>r = r \<and> \<acute>parent_edge = p \<and> \<acute>num = n
      \<and> \<acute>R = parent_num_assms_inv \<acute>G \<acute>r \<acute>parent_edge \<acute>num (ivertex_cnt \<acute>G)\<rbrace>"

procedures check_connected (G :: IGraph, r :: IVertex, parent_edge :: IPEdge,
    num :: INum | R :: bool)
  where
    R1 :: bool
    R2 :: bool
    R3 :: bool
  in "
    \<acute>R1 :== CALL is_wellformed(\<acute>G) ;;
    \<acute>R2 :== \<acute>r < ivertex_cnt \<acute>G \<and> \<acute>num \<acute>r = 0 \<and> \<acute>parent_edge \<acute>r = None ;;
    \<acute>R3 :== CALL parent_num_assms(\<acute>G, \<acute>r, \<acute>parent_edge, \<acute>num) ;;
    \<acute>R :== \<acute>R1 \<and> \<acute>R2 \<and> \<acute>R3"

end

