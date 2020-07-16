theory Counting imports Main begin

section "https://principia.connpass.com/event/182988/"
subsection "Q1"

fun count_pos :: "int list \<Rightarrow> nat" where
  count_pos_Nil: "count_pos [] = 0" |
  count_pos_Cons: "count_pos (x#xs) = (if x > 0 then Suc (count_pos xs) else count_pos xs)"

lemma count_pos_append: "count_pos (xs@ys) = (count_pos xs) + (count_pos ys)"
  apply(induct xs)
  apply(auto)
  done


subsection "Q2"

lemma Collect_cong_UnR: "(\<And>i. P i = (R i \<or> Q i)) \<Longrightarrow> {i. P i} = {i. R i} \<union> {i. Q i}"
  apply(auto)
  done

lemma lt_Suc_iff: "(i < Suc n) = (i < n \<or> i = n)"
  apply(auto)
  done

lemma nth_append_iff: "(i < length xs \<and> P ((xs @ [x]) ! i)) = (i < length xs \<and> P (xs!i))"
  apply(subst nth_append)
  apply(auto)
  done

lemma nth_append_iff_UnR: "{i. i < length (xs@[x]) \<and> P ((xs@[x])!i) }
     = {i. i < length xs \<and> P (xs!i) } \<union> { i. i = length xs \<and> P x }" for P::"'a \<Rightarrow> bool"
  apply(rule Collect_cong_UnR)
  apply(simp)
  apply(subst lt_Suc_iff)
  apply(subst conj_disj_distribR)
  apply(subst nth_append_iff)
  apply(subst nth_append)
  apply(auto)
  done

lemma idx_set_disjoint: "{i. i < length xs \<and> 0 < xs ! i} \<inter> {i. i = length xs \<and> 0 < x} = {}"
  apply(auto)
  done

lemma ab_cd_eq_a_cdb: "a + b = c + d \<Longrightarrow> a = c + d - b" for a::nat and b::nat and c::nat and d::nat
  apply(auto)
  done

lemma card_Un_iff: "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> card (A \<union> B) = card A + card B - card (A \<inter> B)"
  apply(rule ab_cd_eq_a_cdb)
  apply(rule sym)
  apply(erule card_Un_Int)
  apply(assumption)
  done

theorem "card {i. i < length xs \<and> xs ! i > 0} = count_pos xs"
  apply(rule rev_induct)
  apply(simp)
  apply(subst nth_append_iff_UnR)
  apply(subst card_Un_iff)
  apply(simp)
  apply(simp)
  apply(subst idx_set_disjoint)
  apply(simp)
  apply(subst count_pos_append)
  apply(subst count_pos_Cons)
  apply(case_tac "0 < x")
  apply(simp)
  apply(simp)
  done
end