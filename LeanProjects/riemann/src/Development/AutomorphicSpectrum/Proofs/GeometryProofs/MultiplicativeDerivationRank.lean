import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PowerDerivation

open Polynomial

theorem exists_natCast_of_pow_eq (k : Type) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (μ : k) (h : μ ^ p = μ) : ∃ i < p, μ = (i : k) := by
  classical
  have hone : 1 < p := hp.out.one_lt
  have hP : (X ^ p - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hone
  have hdeg : (X ^ p - X : k[X]).natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq k hone
  haveI : ExpChar k p := ExpChar.prime hp.out
  set S : Finset k := (Finset.range p).image (fun i : ℕ => (i : k)) with hS
  have hcard : S.card = p := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact CharP.natCast_injOn_Iio k p (by simpa using ha) (by simpa using hb) hab
  have hsub : S ⊆ (X ^ p - X : k[X]).roots.toFinset := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    have hi : ((i : k)) ^ p = i := by
      have := map_natCast (frobenius k p) i
      rwa [frobenius_def] at this
    rw [Multiset.mem_toFinset, mem_roots hP]
    simp [IsRoot, hi]
  have hEq : S = (X ^ p - X : k[X]).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard]
    calc _ ≤ Multiset.card (X ^ p - X : k[X]).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ = p := hdeg
  have hμ : μ ∈ S := by
    rw [hEq, Multiset.mem_toFinset, mem_roots hP]
    simp [IsRoot, h]
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hμ
  exact ⟨i, Finset.mem_range.1 hi, rfl⟩

theorem iSup_eigenspace_eq_top (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] (R : Type) [AddCommGroup R] [Module k R] [Module.Finite k R]
    (T : Module.End k R) (h : ∀ a : R, (⇑T)^[p] a = T a) :
    ⨆ μ : k, T.eigenspace μ = ⊤ := by
  have hsep : (X ^ p - X : k[X]).Separable := galois_poly_separable p p dvd_rfl
  have h0 : aeval T (X ^ p - X : k[X]) = 0 := by
    ext a
    simp [Module.End.pow_apply, h a]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree h0
  have := Module.End.iSup_maxGenEigenspace_eq_top T
  simpa [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using this

section Main

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

noncomputable def powerSum (D : Derivation k R R) (z : R) (p : ℕ) :
    (Fin p → LinearMap.ker (D : R →ₗ[k] R)) →ₗ[k] R where
  toFun a := ∑ i, (a i : R) * z ^ (i : ℕ)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

theorem powerSum_apply (D : Derivation k R R) (z : R) (p : ℕ)
    (a : Fin p → LinearMap.ker (D : R →ₗ[k] R)) :
    powerSum D z p a = ∑ i, (a i : R) * z ^ (i : ℕ) := rfl

theorem derivation_pow_of_eq (D : Derivation k R R) {z : R} (hz : D z = z) (n : ℕ) :
    D (z ^ n) = (n : R) * z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, D.leibniz, ih, hz]
    simp only [smul_eq_mul]
    push_cast
    ring

theorem derivation_inv_of_eq (D : Derivation k R R) {z w : R} (hz : D z = z) (hw : z * w = 1) :
    D w = -w := by
  have h1 : D (z * w) = 0 := by rw [hw]; simp
  rw [D.leibniz, hz] at h1
  simp only [smul_eq_mul] at h1
  have h2 : w * (z * D w + w * z) = 0 := by rw [h1, mul_zero]
  have h3 : w * (z * D w + w * z) = (z * w) * D w + (z * w) * w := by ring
  rw [h3, hw] at h2
  linear_combination h2

theorem derivation_inv_pow_of_eq (D : Derivation k R R) {z w : R} (hz : D z = z)
    (hw : z * w = 1) (n : ℕ) : D (w ^ n) = -(n : R) * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, D.leibniz, ih, derivation_inv_of_eq D hz hw]
    simp only [smul_eq_mul]
    push_cast
    ring

theorem mem_eigenspace_of_mem_ker (D : Derivation k R R) {z : R} (hz : D z = z)
    (a : LinearMap.ker (D : R →ₗ[k] R)) (n : ℕ) :
    (a : R) * z ^ n ∈ Module.End.eigenspace (D : R →ₗ[k] R) (n : k) := by
  have ha : D (a : R) = 0 := a.2
  rw [Module.End.mem_eigenspace_iff]
  change D ((a : R) * z ^ n) = _
  rw [D.leibniz, derivation_pow_of_eq D hz, ha, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  simp only [smul_eq_mul, smul_zero, add_zero]
  ring

theorem powerSum_injective (p : ℕ) [CharP k p] (D : Derivation k R R) {z w : R}
    (hz : D z = z) (hw : z * w = 1) : Function.Injective (powerSum D z p) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hinj : Function.Injective (fun i : Fin p => ((i : ℕ) : k)) := fun i j hij =>
    Fin.ext (CharP.natCast_injOn_Iio k p i.2 j.2 hij)
  have hind := (Module.End.eigenspaces_iSupIndep (D : R →ₗ[k] R)).comp hinj
  have h0 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ
    (fun i => (a i : R) * z ^ (i : ℕ)) (fun i _ => mem_eigenspace_of_mem_ker D hz (a i) i) ha
  funext i
  have h1 := h0 i (Finset.mem_univ i)
  apply Subtype.ext
  have h2 : (a i : R) * z ^ (i : ℕ) * w ^ (i : ℕ) = a i := by
    rw [mul_assoc, ← mul_pow, hw, one_pow, mul_one]
  simpa [h1] using h2.symm

theorem powerSum_single (D : Derivation k R R) (z : R) (p : ℕ) (i : Fin p)
    (x : LinearMap.ker (D : R →ₗ[k] R)) :
    powerSum D z p (Pi.single i x) = (x : R) * z ^ (i : ℕ) := by
  classical
  rw [powerSum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem powerSum_surjective [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    [Module.Finite k R] (D : Derivation k R R) (hD : ∀ a : R, (⇑D)^[p] a = D a) {z w : R}
    (hz : D z = z) (hw : z * w = 1) : Function.Surjective (powerSum D z p) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← iSup_eigenspace_eq_top k p R (D : R →ₗ[k] R) hD, iSup_le_iff]
  intro μ v hv
  by_cases hv0 : v = 0
  · rw [hv0]; exact Submodule.zero_mem _
  have hev : Module.End.HasEigenvector (D : R →ₗ[k] R) μ v := ⟨hv, hv0⟩
  have hμ : μ ^ p = μ := by
    have h1 := hev.pow_apply p
    rw [Module.End.pow_apply] at h1
    have h2 : (⇑(D : R →ₗ[k] R))^[p] v = D v := hD v
    rw [h2] at h1
    have h3 : D v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    rw [h3] at h1
    exact (smul_left_injective k hv0 h1).symm
  obtain ⟨i, hi, rfl⟩ := exists_natCast_of_pow_eq k p μ hμ
  have h3 : D v = (i : R) * v := by
    rw [show D v = ((i : ℕ) : k) • v from Module.End.mem_eigenspace_iff.1 hv,
      Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hx : v * w ^ i ∈ LinearMap.ker (D : R →ₗ[k] R) := by
    change D (v * w ^ i) = 0
    rw [D.leibniz, derivation_inv_pow_of_eq D hz hw, h3]
    simp only [smul_eq_mul]
    ring
  refine ⟨Pi.single ⟨i, hi⟩ ⟨v * w ^ i, hx⟩, ?_⟩
  rw [powerSum_single]
  change v * w ^ i * z ^ i = v
  rw [mul_assoc, ← mul_pow, mul_comm w z, hw, one_pow, mul_one]

theorem map_powerSum_eq_zero (D : Derivation k R R) (ε : R →ₐ[k] k) {z : R} (p : ℕ)
    (u : R →ₗ[k] k) (hu : ∀ a b : R, u (a * b) = u a * ε b + ε a * u b)
    (hk : ∀ a : R, D a = 0 → u a = 0) (huz : u z = 0)
    (a : Fin p → LinearMap.ker (D : R →ₗ[k] R)) : u (powerSum D z p a) = 0 := by
  have hpow : ∀ n : ℕ, u (z ^ n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hk 1 (by simp)
    | succ n ih => rw [pow_succ, hu, ih, huz]; simp
  rw [powerSum_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hu, hpow, hk _ (a i).2]
  simp

theorem finrank_eq_and_derivation_eq_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = D a) → ∀ z₀ : R, IsUnit z₀ → D z₀ = z₀ →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  intro k _ _ p _ _ R _ _ _ D ε hD z₀ hu hz
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hinj := powerSum_injective p D hz hw
  have hsurj := powerSum_surjective p D hD hz hw
  refine ⟨?_, z₀, ?_, ?_⟩
  · rw [← (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_pi_fintype]
    simp
  · rw [hz]
    exact (hu.map ε).ne_zero
  · intro u h1 h2 h3
    ext r
    obtain ⟨a, rfl⟩ := hsurj r
    simpa using map_powerSum_eq_zero D ε p u h1 h2 h3 a

end Main

end GlobalTheory.CompanionTheory.PowerDerivation
