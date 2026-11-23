import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {ι E : Type} [LinearOrder ι] [AddCommGroup E]

private def tS (S : Finset ι) (k : ι) : ℤ := ∏ x ∈ S, if x < k then -1 else 1

private def uS (S : Finset ι) (k : ι) : ℤ := ∏ x ∈ S, if k < x then -1 else 1

private def shS (I J : Finset ι) : ℤ := ∏ i ∈ I, tS J i

private theorem cs_eq (S : Finset ι) (k : ι) : GlobalTheory.cubeSign S k = tS S k := by
  unfold GlobalTheory.cubeSign tS
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private theorem tS_sq (S : Finset ι) (k : ι) : tS S k * tS S k = 1 := by
  unfold tS
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro x _
  split_ifs <;> norm_num

private theorem tS_union {S T : Finset ι} (h : Disjoint S T) (k : ι) :
    tS (S ∪ T) k = tS S k * tS T k := by
  unfold tS
  rw [Finset.prod_union h]

private theorem tS_erase (S : Finset ι) (k : ι) : tS (S.erase k) k = tS S k := by
  simp only [tS]
  exact Finset.prod_erase _ (by simp)

private theorem tS_mul_uS {S : Finset ι} {k : ι} (h : k ∉ S) : tS S k * uS S k = (-1) ^ S.card := by
  unfold tS uS
  rw [← Finset.prod_mul_distrib]
  trans ∏ _x ∈ S, (-1 : ℤ)
  · apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ k := fun e => h (e ▸ hx)
    rcases lt_or_gt_of_ne hne with hl | hl
    · simp [hl, not_lt.2 hl.le]
    · simp [hl, not_lt.2 hl.le]
  · simp

private theorem sg_left {I : Finset ι} (J : Finset ι) {k : ι} (h : k ∈ I) :
    shS I J = tS J k * shS (I.erase k) J := by
  unfold shS
  exact (Finset.mul_prod_erase I (fun i => tS J i) h).symm

private theorem sg_eq_u (I J : Finset ι) : shS I J = ∏ j ∈ J, uS I j := by
  unfold shS tS uS
  exact Finset.prod_comm

private theorem sg_right (I : Finset ι) {J : Finset ι} {k : ι} (h : k ∈ J) :
    shS I J = uS I k * shS I (J.erase k) := by
  rw [sg_eq_u, sg_eq_u]
  exact (Finset.mul_prod_erase J (fun j => uS I j) h).symm

private def ah (α : Finset ι → E) (I J : Finset ι) : E :=
  if Disjoint I J then shS I J • α (I ∪ J) else 0

private theorem ah_cocycle (α : Finset ι → E)
    (h : ∀ s : Finset ι, ∑ k ∈ s, GlobalTheory.cubeSign s k • α (s.erase k) = 0) (I J : Finset ι) :
    ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J +
      ((-1 : ℤ) ^ I.card) • ∑ j ∈ J, GlobalTheory.cubeSign J j • ah α I (J.erase j) = 0 := by
  by_cases hd : Disjoint I J
  · have e1 : ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J =
        ∑ i ∈ I, shS I J • (GlobalTheory.cubeSign (I ∪ J) i • α ((I ∪ J).erase i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiJ : i ∉ J := Finset.disjoint_left.1 hd hi
      have hdi : Disjoint (I.erase i) J :=
        Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd
      have hset : I.erase i ∪ J = (I ∪ J).erase i := by
        ext y
        by_cases hy : y = i <;> simp [hy, hiJ]
      unfold ah
      rw [if_pos hdi, hset, smul_smul, smul_smul]
      congr 1
      rw [cs_eq, cs_eq, tS_union hd, sg_left J hi]
      linear_combination (-(tS I i * shS (I.erase i) J)) * tS_sq J i
    have e2 : ∑ j ∈ J, ((-1 : ℤ) ^ I.card) • (GlobalTheory.cubeSign J j • ah α I (J.erase j)) =
        ∑ j ∈ J, shS I J • (GlobalTheory.cubeSign (I ∪ J) j • α ((I ∪ J).erase j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjI : j ∉ I := Finset.disjoint_right.1 hd hj
      have hdj : Disjoint I (J.erase j) :=
        Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd
      have hset : I ∪ J.erase j = (I ∪ J).erase j := by
        ext y
        by_cases hy : y = j <;> simp [hy, hjI]
      unfold ah
      rw [if_pos hdj, hset, smul_smul, smul_smul, smul_smul]
      congr 1
      rw [cs_eq, cs_eq, tS_union hd, sg_right I hj]
      linear_combination (-(tS J j * shS I (J.erase j))) * tS_mul_uS hjI
    rw [e1, Finset.smul_sum, e2, ← Finset.smul_sum, ← Finset.smul_sum, ← smul_add,
      ← Finset.sum_union hd, h, smul_zero]
  · obtain ⟨x, hxI, hxJ⟩ := Finset.not_disjoint_iff.1 hd
    have hsym : Disjoint I (J.erase x) ↔ Disjoint (I.erase x) J := by
      rw [Finset.disjoint_left, Finset.disjoint_left]
      constructor
      · intro h' y hy hyJ
        exact h' (Finset.mem_of_mem_erase hy) (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hy, hyJ⟩)
      · intro h' y hyI hy
        exact h' (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hy, hyI⟩) (Finset.mem_of_mem_erase hy)
    have e1 : ∑ i ∈ I, GlobalTheory.cubeSign I i • ah α (I.erase i) J =
        GlobalTheory.cubeSign I x • ah α (I.erase x) J := by
      refine Finset.sum_eq_single_of_mem x hxI fun i _ hne => ?_
      unfold ah
      rw [if_neg, smul_zero]
      intro hdi
      exact Finset.disjoint_left.1 hdi (Finset.mem_erase.2 ⟨hne.symm, hxI⟩) hxJ
    have e2 : ∑ j ∈ J, GlobalTheory.cubeSign J j • ah α I (J.erase j) =
        GlobalTheory.cubeSign J x • ah α I (J.erase x) := by
      refine Finset.sum_eq_single_of_mem x hxJ fun j _ hne => ?_
      unfold ah
      rw [if_neg, smul_zero]
      intro hdj
      exact Finset.disjoint_left.1 hdj hxI (Finset.mem_erase.2 ⟨hne.symm, hxJ⟩)
    rw [e1, e2]
    by_cases hd2 : Disjoint (I.erase x) J
    · have hd3 : Disjoint I (J.erase x) := hsym.2 hd2
      have s1 : I.erase x ∪ J = I ∪ J := by
        ext y
        by_cases hy : y = x <;> simp [hy, hxJ]
      have s2 : I ∪ J.erase x = I ∪ J := by
        ext y
        by_cases hy : y = x <;> simp [hy, hxI]
      unfold ah
      rw [if_pos hd2, if_pos hd3, s1, s2, smul_smul, smul_smul, smul_smul, ← add_smul]
      have hnot : x ∉ I.erase x := fun h' => Finset.ne_of_mem_erase h' rfl
      obtain ⟨n, hn⟩ : ∃ n, I.card = n + 1 :=
        Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero_of_mem hxI)
      have hcard : (I.erase x).card = n := by
        rw [Finset.card_erase_of_mem hxI, hn, Nat.add_sub_cancel]
      have h1 := tS_mul_uS hnot
      rw [hcard] at h1
      have h2 := tS_sq J x
      have hz : GlobalTheory.cubeSign I x * shS (I.erase x) J +
          (-1 : ℤ) ^ I.card * GlobalTheory.cubeSign J x * shS I (J.erase x) = 0 := by
        rw [cs_eq, cs_eq, sg_right (I.erase x) hxJ, sg_left (J.erase x) hxI, tS_erase,
          ← tS_erase I x, hn]
        linear_combination (shS (I.erase x) (J.erase x)) * h1 +
          ((-1 : ℤ) ^ (n + 1) * shS (I.erase x) (J.erase x)) * h2
      rw [hz, zero_smul]
    · unfold ah
      rw [if_neg hd2, if_neg (fun h' => hd2 (hsym.1 h'))]
      simp

private theorem sum_single (I : Finset ι) (x : E) :
    ∑ i ∈ I, GlobalTheory.cubeSign I i • (if I.erase i = ∅ then x else 0) = if I.card = 1 then x else 0 := by
  split_ifs with h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    simp [GlobalTheory.cubeSign_singleton]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg, smul_zero]
    intro he
    apply h
    have h3 := Finset.card_erase_of_mem hi
    rw [he, Finset.card_empty] at h3
    have h4 := Finset.card_pos.2 ⟨i, hi⟩
    omega

private theorem wd_ap [Module ℂ E] (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]
end

theorem UpperTheory.Gal.productCup_of_system.edgeRel_of :
    WdUni → EdgeRel := by
  intro hU
  unfold EdgeRel
  intro ι E _ _ _ _ G p _ α hα
  unfold cech Cx.Z at hα
  simp [cechC] at hα
  obtain ⟨hC, hδ⟩ := hα
  have hcoc : ∀ s : Finset ι, ∑ k ∈ s, GlobalTheory.cubeSign s k • α (s.erase k) = 0 := by
    intro s
    simpa [deltaL, GlobalTheory.DI.delta] using congrFun hδ s
  have hα0 : α ∅ = 0 := by simpa using hC ∅
  have hl : ∀ a b : Finset ι, lft (uni a b) = a := fun a b =>
    (hU ι ι E (fun _ => 1) (fun _ => 0) a b).2.1
  have hr : ∀ a b : Finset ι, rgt (uni a b) = b := fun a b =>
    (hU ι ι E (fun _ => 1) (fun _ => 0) a b).2.2.1
  have hsurj : ∀ s : Finset (ι ⊕ₗ ι), ∃ I J, s = uni I J := fun s =>
    ⟨lft s, rgt s, ((hU ι ι E (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s).symm⟩
  have key : ∀ I : Finset ι, ((-1 : ℤ) ^ I.card) • α I = -(((-1 : ℤ) ^ p) • α I) := by
    intro I
    by_cases hI : I.Nonempty ∧ ((I.card : ℕ) : ℤ) = (p : ℤ) + 1
    · have e : I.card = p + 1 := by omega
      rw [e, pow_succ, mul_neg_one, neg_smul]
    · have h0 := hC I
      rw [if_neg hI] at h0
      have h1 : α I = 0 := by simpa using h0
      simp [h1]
  obtain ⟨c, hc⟩ : ∃ c : Finset (ι ⊕ₗ ι) → E, ∀ s, c s =
      if (lft s).Nonempty ∧ (rgt s).Nonempty then -ah α (lft s) (rgt s) else 0 :=
    ⟨_, fun s => rfl⟩
  unfold acx Cx.B
  refine Submodule.mem_map.2 ⟨c, ?_, ?_⟩
  · dsimp only
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
    intro s
    obtain ⟨I, J, rfl⟩ := hsurj s
    rw [hc, hl, hr]
    have hcardU := (hU ι ι E (fun _ => 1) (fun _ => 0) I J).2.2.2.1
    by_cases hIJ : I.Nonempty ∧ J.Nonempty
    · rw [if_pos hIJ]
      unfold ah
      by_cases hd : Disjoint I J
      · rw [if_pos hd]
        have hα' := hC (I ∪ J)
        by_cases hcd : (I ∪ J).Nonempty ∧ (((I ∪ J).card : ℕ) : ℤ) = (p : ℤ) + 1
        · rw [if_pos hcd] at hα'
          have hk : (((uni I J).card : ℕ) : ℤ) = (p : ℤ) + 2 - 1 := by
            rw [hcardU, ← Finset.card_union_of_disjoint hd]
            have := hcd.2
            omega
          rw [if_pos hk]
          simp only [mixF, hl, hr, if_pos hIJ]
          exact neg_mem (zsmul_mem hα' _)
        · rw [if_neg hcd] at hα'
          have h0 : α (I ∪ J) = 0 := by simpa using hα'
          rw [h0, smul_zero, neg_zero]
          exact Submodule.zero_mem _
      · rw [if_neg hd, neg_zero]
        exact Submodule.zero_mem _
    · rw [if_neg hIJ]
      exact Submodule.zero_mem _
  · dsimp only
    funext s
    obtain ⟨I, J, rfl⟩ := hsurj s
    have h := hU ι ι E (fun _ => 1) c I J
    rw [h.1, wd_ap, wd_ap]
    simp only [hc, hl, hr, edge1, edge2, Pi.sub_apply, Pi.smul_apply, Module.End.one_apply]
    by_cases hJ : J.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty] at hJ
      subst hJ
      simp [hα0]
    by_cases hI : I.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty] at hI
      subst hI
      simp [hα0]
    have t1 : ∀ i ∈ I, GlobalTheory.cubeSign I i •
        (if (I.erase i).Nonempty ∧ J.Nonempty then -ah α (I.erase i) J else 0) =
        -(GlobalTheory.cubeSign I i • ah α (I.erase i) J) +
          GlobalTheory.cubeSign I i • (if I.erase i = ∅ then α J else 0) := by
      intro i _
      by_cases he : I.erase i = ∅
      · rw [he]
        simp [ah, shS]
      · have hne : (I.erase i).Nonempty := Finset.nonempty_iff_ne_empty.2 he
        rw [if_pos ⟨hne, hJ⟩, if_neg he, smul_zero, add_zero, smul_neg]
    have t2 : ∀ j ∈ J, GlobalTheory.cubeSign J j •
        (if I.Nonempty ∧ (J.erase j).Nonempty then -ah α I (J.erase j) else 0) =
        -(GlobalTheory.cubeSign J j • ah α I (J.erase j)) +
          GlobalTheory.cubeSign J j • (if J.erase j = ∅ then α I else 0) := by
      intro j _
      by_cases he : J.erase j = ∅
      · rw [he]
        simp [ah, shS, tS]
      · have hne : (J.erase j).Nonempty := Finset.nonempty_iff_ne_empty.2 he
        rw [if_pos ⟨hI, hne⟩, if_neg he, smul_zero, add_zero, smul_neg]
    rw [Finset.sum_congr rfl t1, Finset.sum_congr rfl t2, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_neg_distrib, sum_single,
      sum_single]
    have hco := ah_cocycle α hcoc I J
    rw [eq_neg_of_add_eq_zero_left hco, smul_add, smul_neg]
    by_cases hJ1 : J.card = 1
    · rw [if_pos hJ1, key]
      abel
    · rw [if_neg hJ1]
      simp only [smul_zero, add_zero, sub_zero]
      abel
