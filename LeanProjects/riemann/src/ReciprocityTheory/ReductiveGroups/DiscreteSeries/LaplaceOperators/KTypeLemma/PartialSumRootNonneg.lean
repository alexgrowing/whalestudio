import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Wt

theorem partialSum_finset_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) (k : ℕ) :
    kirrPs k (∑ i ∈ s, f i) = ∑ i ∈ s, kirrPs k (f i) := by
  simp only [kirrPs, Finset.sum_apply]
  exact Finset.sum_comm

theorem rootCone_entry_int (k : ℕ) (μ ν : Fin n → ℝ) : kirrPs k (μ + ν) = kirrPs k μ + kirrPs k ν := by
  simp only [kirrPs, Pi.add_apply, Finset.sum_add_distrib]

theorem partialSum_sub (k : ℕ) (μ ν : Fin n → ℝ) : kirrPs k (μ - ν) = kirrPs k μ - kirrPs k ν := by
  simp only [kirrPs, Pi.sub_apply, Finset.sum_sub_distrib]

theorem partialSum_smul (k : ℕ) (c : ℝ) (μ : Fin n → ℝ) : kirrPs k (c • μ) = c * kirrPs k μ := by
  simp only [kirrPs, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem partialSum_single (k : ℕ) (a : Fin n) :
    kirrPs k (Pi.single a (1 : ℝ)) = if a.val < k then 1 else 0 := by
  simp only [kirrPs, Finset.sum_pi_single', Finset.mem_filter, Finset.mem_univ, true_and]

theorem highestWeightVector_lift (k : ℕ) (a : Fin n) :
    0 ≤ kirrPs k (Pi.single a (1 : ℝ)) ∧ kirrPs k (Pi.single a (1 : ℝ)) ≤ 1 := by
  rw [partialSum_single]
  split_ifs <;> norm_num

theorem partialSum_root_nonneg {a b : Fin n} (hab : a < b) (k : ℕ) : 0 ≤ kirrPs k (root a b) := by
  have hv : a.val < b.val := hab
  rw [show root a b = Pi.single a (1 : ℝ) - Pi.single b 1 from rfl, partialSum_sub, partialSum_single, partialSum_single]
  split_ifs with h1 h2 h2
  · norm_num
  · norm_num
  · exfalso; omega
  · norm_num

theorem partialSum_single_bounds {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : 0 ≤ kirrPs k β := by
  obtain ⟨m, rfl⟩ := hβ
  rw [partialSum_finset_sum_eq]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [partialSum_finset_sum_eq]
  refine Finset.sum_nonneg fun b _ => ?_
  split_ifs with h
  · rw [partialSum_smul]
    exact mul_nonneg (Nat.cast_nonneg _) (partialSum_root_nonneg h k)
  · simp [kirrPs]

theorem partialSum_add_eq {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    kUnitWtLin (∑ i ∈ s, f i) = ∑ i ∈ s, kUnitWtLin (f i) := by
  simp only [kUnitWtLin, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem unitWeightSum_sub (μ ν : Fin n → ℝ) : kUnitWtLin (μ - ν) = kUnitWtLin μ - kUnitWtLin ν := by
  simp only [kUnitWtLin, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem unitWeightSum_smul (c : ℝ) (μ : Fin n → ℝ) : kUnitWtLin (c • μ) = c * kUnitWtLin μ := by
  simp only [kUnitWtLin, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem unitWeightSum_finset_sum {a b : Fin n} (hab : a < b) :
    kUnitWtLin (root a b) = (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) := by
  have hv : (a : ℕ) ≤ (b : ℕ) := le_of_lt (show (a : ℕ) < b from hab)
  rw [show root a b = Pi.single a (1 : ℝ) - Pi.single b 1 from rfl, unitWeightSum_sub, Nat.cast_sub hv]
  simp only [kUnitWtLin, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem tensorAction_ofLp {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, kUnitWtLin β = N := by
  obtain ⟨m, rfl⟩ := hβ
  refine ⟨∑ a, ∑ b, if a < b then m a b * ((b : ℕ) - (a : ℕ)) else 0, ?_⟩
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  rw [partialSum_add_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [partialSum_add_eq]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [unitWeightSum_smul, unitWeightSum_finset_sum h]
  · simp [kUnitWtLin]

theorem rootCone_unitWeightSum_nat {β : Fin n → ℝ} (hβ : InRootCone β) (c : Fin n) : ∃ z : ℤ, β c = z := by
  obtain ⟨m, rfl⟩ := hβ
  refine ⟨∑ a, ∑ b, if a < b then (m a b : ℤ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) else 0, ?_⟩
  simp only [Finset.sum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a < b
  · simp only [h, if_true, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub,
      apply_ite (Int.cast : ℤ → ℝ), Int.cast_one, Int.cast_zero, root, Pi.sub_apply, Pi.single_apply]
  · simp only [h, if_false, Pi.zero_apply, Int.cast_zero]

theorem unitWeightSum_root (μ : Fin n → ℝ) (a : Fin n) : kirrPs (a.val + 1) μ = μ a + kirrPs a.val μ := by
  unfold kirrPs
  have hs : (univ.filter fun x : Fin n => x.val < a.val + 1) =
      Finset.cons a (univ.filter fun x : Fin n => x.val < a.val) (by simp) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons, Fin.ext_iff]
    omega
  rw [hs, Finset.sum_cons]

theorem aux_statement_19 {β : Fin n → ℝ} (h0 : ∀ k, 0 ≤ kirrPs k β) (h1 : ∀ k, kirrPs k β ≤ 1)
    (a : Fin n) : -1 ≤ β a ∧ β a ≤ 1 := by
  have h := unitWeightSum_root β a
  have h2 := h0 (a.val + 1)
  have h3 := h1 (a.val + 1)
  have h4 := h0 a.val
  have h5 := h1 a.val
  constructor <;> linarith

end Wt

section Dom

theorem highestWeight_dominant {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] {ε : Fin n → Bool}
    {A : Fin n → Fin n → Module.End ℂ N} (hA : IsGlRep A) (hU : IsKUnitary ε A) {ν : Fin n → ℝ}
    {y : N} (hy0 : y ≠ 0) (hy : IsKHWVec ε A ν y) {a b : Fin n} (hab : a < b) (hε : ε a = ε b) :
    ν b ≤ ν a := by
  have h0 : A a b y = 0 := hy.2 a b hab hε
  have hc : A a b (A b a y) = ((ν a - ν b : ℝ) : ℂ) • y := by
    have h := LinearMap.congr_fun (hA a b b a) y
    simp only [LinearMap.sub_apply, Module.End.mul_apply, h0, map_zero, sub_zero, if_true, hy.1] at h
    rw [h, Complex.ofReal_sub, sub_smul]
  have key : inner ℂ (A a b (A b a y)) y = inner ℂ (A b a y) (A b a y) := hU a b hε _ _
  rw [hc, inner_smul_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal] at key
  have key' : (ν a - ν b) * ‖y‖ ^ 2 = ‖A b a y‖ ^ 2 := by
    norm_cast at key
    first
    | exact Complex.ofReal_injective key
    | exact RCLike.ofReal_injective key
    | exact (Complex.ofReal_injective (by simpa using key))
  have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
  by_contra hlt
  push_neg at hlt
  have := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos
  nlinarith [sq_nonneg ‖A b a y‖]

theorem rho_adjacent_same_sign {ε : Fin n → Bool} {a b : Fin n} (hab : a.val + 1 = b.val) (hε : ε a = ε b) :
    rhoC ε a - rhoC ε b = 1 ∧ rhoN ε a = rhoN ε b := by
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have e1 : (univ.filter fun c => a < c ∧ ε c = ε a) =
      Finset.cons b (univ.filter fun c => b < c ∧ ε c = ε b) (by simp) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : c = b
      · exact Or.inl hc
      · have hne : c.val ≠ b.val := fun h => hc (Fin.ext h)
        refine Or.inr ⟨?_, h2.trans hε⟩
        rw [Fin.lt_def] at h1 ⊢
        omega
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨hab', hε.symm⟩
      · exact ⟨hab'.trans h1, h2.trans hε.symm⟩
  have e2 : (univ.filter fun c => c < b ∧ ε c = ε b) =
      Finset.cons a (univ.filter fun c => c < a ∧ ε c = ε a) (by simp) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hc : c = a
      · exact Or.inl hc
      · have hne : c.val ≠ a.val := fun h => hc (Fin.ext h)
        refine Or.inr ⟨?_, h2.trans hε.symm⟩
        rw [Fin.lt_def] at h1 ⊢
        omega
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨hab', hε⟩
      · exact ⟨h1.trans hab', h2.trans hε⟩
  have e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hc : c ≠ b := by rintro rfl; exact h2 hε.symm
      have hne : c.val ≠ b.val := fun h => hc (Fin.ext h)
      refine ⟨?_, fun h => h2 (h.trans hε.symm)⟩
      rw [Fin.lt_def] at h1 ⊢
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨hab'.trans h1, fun h => h2 (h.trans hε)⟩
  have e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hc : c ≠ a := by rintro rfl; exact h2 hε
      have hne : c.val ≠ a.val := fun h => hc (Fin.ext h)
      refine ⟨?_, fun h => h2 (h.trans hε)⟩
      rw [Fin.lt_def] at h1 ⊢
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans hab', fun h => h2 (h.trans hε.symm)⟩
  refine ⟨?_, ?_⟩
  · simp only [rhoC]
    rw [e1, e2, Finset.card_cons, Finset.card_cons]
    push_cast
    ring
  · simp only [rhoN]
    rw [e3, e4]

end Dom

section Irr

theorem exists_minimal_kStable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
    {A : Fin n → Fin n → Module.End ℂ X} {S : Submodule ℂ X} (hfd : FiniteDimensional ℂ S)
    (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ W ≤ S, W ≠ ⊥ ∧ IsKStableSub ε A W ∧
      ∀ W' : Submodule ℂ X, W' ≤ W → IsKStableSub ε A W' → W' = ⊥ ∨ W' = W := by
  classical
  have hex : ∃ d, ∃ W : Submodule ℂ X, W ≤ S ∧ W ≠ ⊥ ∧ IsKStableSub ε A W ∧ Module.finrank ℂ W = d :=
    ⟨_, S, le_rfl, hne, hS, rfl⟩
  obtain ⟨W, hWS, hW0, hWst, hWd⟩ := Nat.find_spec hex
  refine ⟨W, hWS, hW0, hWst, fun W' hW'W hW'st => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hlt : W' < W := lt_of_le_of_ne hW'W h2
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  have hr := Submodule.finrank_lt_finrank_of_lt hlt
  exact Nat.find_min hex (by rw [← hWd]; exact hr) ⟨W', hW'W.trans hWS, h1, hW'st, rfl⟩

private theorem k3a_joint_lemma {N : Type*} [AddCommGroup N] [Module ℂ N] (T : Fin n → Module.End ℂ N)
    (hc : ∀ i j x, T i (T j x) = T j (T i x)) (s : Finset (Fin n)) :
    ∀ U : Submodule ℂ N, FiniteDimensional ℂ U → (∀ i, ∀ u ∈ U, T i u ∈ U) → U ≠ ⊥ →
      ∃ u ∈ U, u ≠ 0 ∧ ∀ i ∈ s, ∃ l : ℂ, T i u = l • u := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro U _ _ hne
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨u, hu, hu0, fun i hi => by simp at hi⟩
  · intro j s _ ih U hfd hst hne
    haveI := hfd
    haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((T j).restrict (hst j))
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hl
    obtain ⟨hvm, hvne⟩ := Module.End.hasEigenvector_iff.mp hv
    have hv1 := Module.End.mem_eigenspace_iff.mp hvm
    have hTv : T j (v : N) = l • (v : N) := by
      have h := congrArg Subtype.val hv1
      simpa [LinearMap.restrict_apply] using h
    have hv0 : (v : N) ≠ 0 := fun h => hvne (Subtype.ext h)
    have memU : ∀ x, x ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) ↔ x ∈ U ∧ T j x = l • x := by
      intro x
      simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hUne : U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) ≠ ⊥ := by
      intro h
      have hm : (v : N) ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) := (memU _).mpr ⟨v.2, hTv⟩
      rw [h, Submodule.mem_bot] at hm
      exact hv0 hm
    have hUst : ∀ i, ∀ u ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)),
        T i u ∈ U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) := by
      intro i u hu
      rw [memU] at hu ⊢
      refine ⟨hst i u hu.1, ?_⟩
      rw [hc j i, hu.2, map_smul]
    haveI : FiniteDimensional ℂ (U ⊓ LinearMap.ker (T j - l • (1 : Module.End ℂ N)) : Submodule ℂ N) :=
      Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨u, hu, hu0, hall⟩ := ih _ inferInstance hUst hUne
    rw [memU] at hu
    refine ⟨u, hu.1, hu0, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨l, hu.2⟩
    · exact hall i hi

theorem exists_kIrreducible_highestWeight {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ N} (hA : IsGlRep A) (hU : IsKUnitary ε A)
    {S : Submodule ℂ N} (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ W ≤ S, ∃ ν : Fin n → ℝ, IsKIrrHW ε A ν W := by
  classical
  obtain ⟨W, hWS, hW0, hWst, hWmin⟩ := exists_minimal_kStable hfd hS hne
  haveI hWfd : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨H, hH⟩ : ∃ H : Module.End ℂ N, ∀ x, H x = ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • A c c x :=
    ⟨∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • A c c, fun x => by simp⟩
  have hcomm1 : ∀ a b c x, A c c (A a b x) - A a b (A c c x) =
      (if c = a then A a b x else 0) - (if c = b then A a b x else 0) := by
    intro a b c x
    have h := LinearMap.congr_fun (hA c c a b) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [h]
    by_cases h1 : c = a <;> by_cases h2 : c = b
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have hHr : ∀ a b x, H (A a b x) = A a b (H x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • A a b x := by
    intro a b x
    rw [← sub_eq_iff_eq_add', hH, hH, map_sum, ← Finset.sum_sub_distrib]
    simp only [map_smul, ← smul_sub, hcomm1]
    simp only [smul_sub, smul_ite, smul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← sub_smul]
    congr 1
    ring
  have hcomm : ∀ i j x, A i i (A j j x) = A j j (A i i x) := by
    intro i j x
    have h := hcomm1 j j i x
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hHW : ∀ x ∈ W, H x ∈ W := by
    intro x hx
    rw [hH]
    exact W.sum_mem fun c _ => W.smul_mem _ (hWst c c rfl x hx)
  have hfin := Module.End.finite_hasEigenvalue (H.restrict hHW)
  obtain ⟨μ0, hμ0⟩ := Module.End.exists_eigenvalue (H.restrict hHW)
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image _ (fun z : ℂ => z.re) hfin ⟨μ0, hμ0⟩
  have hbound : ∀ y ∈ W, y ≠ 0 → ∀ z : ℂ, H y = z • y → z.re ≤ μ.re := by
    intro y hy hy0 z hz
    refine hmax z ?_
    show Module.End.HasEigenvalue (H.restrict hHW) z
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨y, hy⟩) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, ?_⟩
    · ext
      simp [LinearMap.restrict_apply, hz]
    · intro h
      apply hy0
      simpa using congrArg Subtype.val h
  have hkill : ∀ u, u ∈ W → H u = μ • u → ∀ a b, a < b → ε a = ε b → A a b u = 0 := by
    intro u huW hHu a b hab he
    by_contra hne'
    have h1 : H (A a b u) = (μ + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ))) • A a b u := by
      rw [hHr a b u, hHu, map_smul, add_smul]
    have h2 := hbound _ (hWst a b he u huW) hne' _ h1
    have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) < b from hab)
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re] at h2
    linarith
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
  obtain ⟨hvm, hvne⟩ := Module.End.hasEigenvector_iff.mp hv
  have hv1 := Module.End.mem_eigenspace_iff.mp hvm
  have hHv : H (v : N) = μ • (v : N) := by
    have h := congrArg Subtype.val hv1
    simpa [LinearMap.restrict_apply] using h
  have hv0 : (v : N) ≠ 0 := fun h => hvne (Subtype.ext h)
  have memU : ∀ x, x ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) ↔ x ∈ W ∧ H x = μ • x := by
    intro x
    simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
  have hUne : W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) ≠ ⊥ := by
    intro h
    have hm : (v : N) ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) := (memU _).mpr ⟨v.2, hHv⟩
    rw [h, Submodule.mem_bot] at hm
    exact hv0 hm
  have hUst : ∀ c, ∀ u ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)),
      A c c u ∈ W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) := by
    intro c u hu
    rw [memU] at hu ⊢
    refine ⟨hWst c c rfl u hu.1, ?_⟩
    rw [hHr c c u, hu.2, map_smul, sub_self, zero_smul, add_zero]
  haveI : FiniteDimensional ℂ (W ⊓ LinearMap.ker (H - μ • (1 : Module.End ℂ N)) : Submodule ℂ N) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨u, hu, hu0, hall⟩ := k3a_joint_lemma (fun c => A c c) hcomm univ _ inferInstance hUst hUne
  rw [memU] at hu
  choose l hl using fun c => hall c (Finset.mem_univ c)
  have hl' : ∀ c, A c c u = l c • u := fun c => hl c
  have hreal : ∀ c, (((l c).re : ℝ) : ℂ) = l c := by
    intro c
    have h1 := hU c c rfl u u
    rw [hl' c, inner_smul_left, inner_smul_right] at h1
    have hne2 : inner ℂ u u ≠ 0 := inner_self_ne_zero.mpr hu0
    exact Complex.conj_eq_iff_re.mp (mul_right_cancel₀ hne2 h1)
  refine ⟨W, hWS, fun c => (l c).re, hWfd, hWst, hWmin, u, hu.1, hu0, fun a => ?_,
    fun a b hab he => hkill u hu.1 hu.2 a b hab he⟩
  rw [hreal a]
  exact hl' a

end Irr

section Lift

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem entry_bounds_of_partialSum {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, h] <;> rfl

def k3aT (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) :
    Module.End ℂ (PiLp 2 fun _ : Fin n => D) :=
  if ε a = ε b then
    (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap ∘ₗ tensV E a b ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin n → D)).toLinearMap
  else 0

theorem tensorAction_apply_eq {a b : Fin n} (hab : ε a = ε b) (x : PiLp 2 fun _ : Fin n => D) :
    WithLp.ofLp (k3aT ε E a b x) = tensV E a b (WithLp.ofLp x) := by
  rw [k3aT, if_pos hab]
  rfl

theorem partialSum_nonneg_rootCone (hU : IsKUnitary ε E) : IsKUnitary ε (k3aT ε E) := by
  intro a b hab x y
  have e1 : ∀ c, WithLp.ofLp (k3aT ε E a b x) c = E a b (WithLp.ofLp x c) + (if c = a then WithLp.ofLp x b else 0) :=
    fun c => by rw [tensorAction_apply_eq hab, entry_bounds_of_partialSum]
  have e2 : ∀ c, WithLp.ofLp (k3aT ε E b a y) c = E b a (WithLp.ofLp y c) + (if c = b then WithLp.ofLp y a else 0) :=
    fun c => by rw [tensorAction_apply_eq hab.symm, entry_bounds_of_partialSum]
  have l : ∀ c, inner ℂ (if c = a then WithLp.ofLp x b else 0) (WithLp.ofLp y c) =
      if c = a then inner ℂ (WithLp.ofLp x b) (WithLp.ofLp y a) else 0 := by
    intro c
    split_ifs with h
    · subst h; rfl
    · exact inner_zero_left _
  have r : ∀ c, inner ℂ (WithLp.ofLp x c) (if c = b then WithLp.ofLp y a else 0) =
      if c = b then inner ℂ (WithLp.ofLp x b) (WithLp.ofLp y a) else 0 := by
    intro c
    split_ifs with h
    · subst h; rfl
    · exact inner_zero_right _
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [e1, e2, inner_add_left, inner_add_right, Finset.sum_add_distrib, l, r, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_congr rfl fun c _ => hU a b hab (WithLp.ofLp x c) (WithLp.ofLp y c)]

end Lift

section Lift2

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem partialSum_succ_alt (hU : IsKUnitary ε E) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (g : (Fin n → D) →ₗ[ℂ] Y) {S : Submodule ℂ (Fin n → D)}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε (tensV E) S)
    (hg : ∀ a b, ε a = ε b → ∀ x ∈ S, g (tensV E a b x) = B a b (g x))
    {x₀ : Fin n → D} (hx₀ : x₀ ∈ S) {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (g x₀)) :
    ∃ x ∈ S, IsKHWVec ε (tensV E) μ x ∧ g x = g x₀ := by
  classical
  have hTe : ∀ a b, ε a = ε b → ∀ v : Fin n → D, k3aT ε E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)).symm v) = (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a b v) := by
    intro a b hab v
    apply (WithLp.linearEquiv 2 ℂ (Fin n → D)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact tensorAction_apply_eq hab _
  haveI hKfd : FiniteDimensional ℂ (S ⊓ LinearMap.ker g : Submodule ℂ (Fin n → D)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℂ (WithLp 2 (Fin n → D)),
      K = (S ⊓ LinearMap.ker g).map ((WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ K := by rw [hK]; infer_instance
  have hmemK : ∀ v, v ∈ S → g v = 0 → (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm v ∈ K := by
    intro v hv hfv
    rw [hK]
    exact Submodule.mem_map_of_mem (Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr hfv⟩)
  have hKmem : ∀ u ∈ K, (WithLp.linearEquiv 2 ℂ (Fin n → D)) u ∈ S ∧ g ((WithLp.linearEquiv 2 ℂ (Fin n → D)) u) = 0 := by
    intro u hu
    rw [hK] at hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    have hv' := Submodule.mem_inf.mp hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact ⟨hv'.1, LinearMap.mem_ker.mp hv'.2⟩
  have hKst : ∀ a b, ε a = ε b → ∀ u ∈ K, k3aT ε E a b u ∈ K := by
    intro a b hab u hu
    obtain ⟨h1, h2⟩ := hKmem u hu
    have e1 : k3aT ε E a b u = (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) u)) := by
      rw [← hTe a b hab, LinearEquiv.symm_apply_apply]
    rw [e1]
    exact hmemK _ (hS a b hab _ h1) (by rw [hg a b hab _ h1, h2, map_zero])
  have hUT := partialSum_nonneg_rootCone hU
  have hperp : ∀ a b, ε a = ε b → ∀ v ∈ Kᗮ, k3aT ε E a b v ∈ Kᗮ := by
    intro a b hab v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← hUT b a hab.symm u v]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hKst b a hab.symm u hu)
  obtain ⟨k, hk, c, hc, hkc⟩ := K.exists_add_mem_mem_orthogonal ((WithLp.linearEquiv 2 ℂ (Fin n → D)).symm x₀)
  obtain ⟨hkS, hkf⟩ := hKmem k hk
  have hx : (WithLp.linearEquiv 2 ℂ (Fin n → D)) c = x₀ - (WithLp.linearEquiv 2 ℂ (Fin n → D)) k := by
    have h3 := congrArg (WithLp.linearEquiv 2 ℂ (Fin n → D)) hkc
    rw [LinearEquiv.apply_symm_apply, map_add] at h3
    rw [h3]
    abel
  have hxS : (WithLp.linearEquiv 2 ℂ (Fin n → D)) c ∈ S := by
    rw [hx]
    exact S.sub_mem hx₀ hkS
  have hfx : g ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) = g x₀ := by rw [hx, map_sub, hkf, sub_zero]
  have hzero : ∀ w, w ∈ S → g w = 0 → (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm w ∈ Kᗮ → w = 0 := by
    intro w hw hfw hpw
    have hm : (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm w ∈ K ⊓ Kᗮ := Submodule.mem_inf.mpr ⟨hmemK w hw hfw, hpw⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.injective (hm.trans (map_zero _).symm)
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin n → D)) c, hxS, ⟨fun a => ?_, fun a b hab he => ?_⟩, hfx⟩
  · have hw : tensV E a a ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) - (μ a : ℂ) • (WithLp.linearEquiv 2 ℂ (Fin n → D)) c ∈ S := S.sub_mem (hS a a rfl _ hxS) (S.smul_mem _ hxS)
    have hfw : g (tensV E a a ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) - (μ a : ℂ) • (WithLp.linearEquiv 2 ℂ (Fin n → D)) c) = 0 := by
      rw [map_sub, map_smul, hg a a rfl _ hxS, hfx, hy.1 a, sub_self]
    have hp : (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a a ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) - (μ a : ℂ) • (WithLp.linearEquiv 2 ℂ (Fin n → D)) c) ∈ Kᗮ := by
      rw [map_sub, map_smul, ← hTe a a rfl, LinearEquiv.symm_apply_apply]
      exact Kᗮ.sub_mem (hperp a a rfl c hc) (Kᗮ.smul_mem _ hc)
    exact sub_eq_zero.mp (hzero _ hw hfw hp)
  · have hw : tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c) ∈ S := hS a b he _ hxS
    have hfw : g (tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c)) = 0 := by rw [hg a b he _ hxS, hfx, hy.2 a b hab he]
    have hp : (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm (tensV E a b ((WithLp.linearEquiv 2 ℂ (Fin n → D)) c)) ∈ Kᗮ := by
      rw [← hTe a b he, LinearEquiv.symm_apply_apply]
      exact hperp a b he c hc
    exact hzero _ hw hfw hp

end Lift2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
