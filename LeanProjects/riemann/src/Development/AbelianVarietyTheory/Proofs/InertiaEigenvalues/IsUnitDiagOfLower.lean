import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.IwahoriRoots

open IsDedekindDomain

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
  [Algebra O E] [IsFractionRing O E]

theorem valuation_unif (ϖ : O) (hϖ : Irreducible ϖ) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E ϖ) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)

theorem valuation_of_isUnit {u : O} (hu : IsUnit u) :
    (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E u) = 1 := by
  obtain ⟨u, rfl⟩ := hu
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  set v := IsDiscreteValuationRing.maximalIdeal O
  have h1 := v.intValuation_le_one (u : O)
  have h2 := v.intValuation_le_one ((u⁻¹ : Oˣ) : O)
  have h3 : v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = v.intValuation (u : O) * v.intValuation ((u⁻¹ : Oˣ) : O) := h3.symm
    _ ≤ v.intValuation (u : O) * 1 := by gcongr
    _ = v.intValuation (u : O) := mul_one _

end Val

theorem isUnit_diag_of_lower {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (x : GL (Fin n) O)
    (hx : ∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O)
    (i : Fin n) : IsUnit ((x : Matrix (Fin n) (Fin n) O) i i) := by
  have h1 : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.map_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hx a b hab)
  have h2 : IsUnit ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det := by
    have e : ((x : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)).det =
        IsLocalRing.residue O (x : Matrix (Fin n) (Fin n) O).det := (RingHom.map_det _ _).symm
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).map _
  rw [Matrix.det_of_upperTriangular h1] at h2
  have h3 := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h2
  simp only [Matrix.map_apply] at h3
  exact isUnit_of_map_unit (IsLocalRing.residue O) _ h3

theorem iwahori_roots : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O), Irreducible ϖ →
    ∀ (n : ℕ) (a : Fin n → ℤ), StrictAnti a → ∀ x y : GL (Fin n) O,
    (∀ i j, j < i → (x : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    (∀ i j, j < i → (y : Matrix (Fin n) (Fin n) O) i j ∈ IsLocalRing.maximalIdeal O) →
    ∃ r : Fin n → E, (∀ i, r i ≠ 0 ∧ val O (r i) = a i) ∧
      ((x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
        Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
        (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E)).charpoly = ∏ i, (X - C (r i)) := by
  intro O _ _ _ _ E _ _ _ _ ϖ hϖ n a ha x y hx hy
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hspan]; exact Ideal.mem_span_singleton_self ϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hspan]; infer_instance
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hϖ0 : algebraMap O E ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨N, hNa⟩ : ∃ N : ℤ, ∀ i, N ≤ a i := by
    obtain ⟨N, hN⟩ := (Set.finite_range a).bddBelow
    exact ⟨N, fun i => hN ⟨i, rfl⟩⟩
  let b : Fin n → ℕ := fun i => (a i - N).toNat
  have hab : ∀ i, a i = N + b i := fun i => by
    have := hNa i
    simp only [b]
    omega
  have hb : StrictAnti b := fun i j h => by
    have := ha h
    rw [hab, hab] at this
    omega
  have hdvd : ∀ z : O, z ∈ IsLocalRing.maximalIdeal O → ϖ ∣ z := fun z hz => by
    rw [hspan] at hz
    exact Ideal.mem_span_singleton.1 hz
  set G : Matrix (Fin n) (Fin n) O :=
    (x : Matrix (Fin n) (Fin n) O) * Matrix.diagonal (fun i => ϖ ^ b i) * y with hG
  have hroot := GlobalTheory.IwahoriEigen.exists_root_of_coeff ϖ hm hb G.charpoly
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) (fun j hj => by
      have := GlobalTheory.IwahoriNewtonTest.intersectionNumber_baseChange O ϖ hm n b hb x y (isUnit_diag_of_lower x hx)
        (isUnit_diag_of_lower y hy) (fun i j h => hdvd _ (hx i j h)) (fun i j h => hdvd _ (hy i j h))
        (n - j) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hj] at this)
  choose z hz hzr using hroot
  set M : Matrix (Fin n) (Fin n) E := (x : Matrix (Fin n) (Fin n) O).map (algebraMap O E) *
    Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) *
    (y : Matrix (Fin n) (Fin n) O).map (algebraMap O E) with hM
  have hMG : M = algebraMap O E ϖ ^ N • G.map (algebraMap O E) := by
    have : Matrix.diagonal (fun i => algebraMap O E ϖ ^ a i) =
        algebraMap O E ϖ ^ N • (Matrix.diagonal (fun i => ϖ ^ b i)).map (algebraMap O E) := by
      rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_smul]
      congr 1
      funext i
      rw [hab, zpow_add₀ hϖ0]
      simp
    rw [hM, this, hG, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
  let r : Fin n → E := fun i => algebraMap O E ϖ ^ N * algebraMap O E (ϖ ^ b i * z i)
  have hr0 : ∀ i, r i ≠ 0 := fun i =>
    mul_ne_zero (zpow_ne_zero _ hϖ0) ((map_ne_zero_iff _ hinj).2
      (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) (hz i).ne_zero))
  have hv : ∀ i, (IsDiscreteValuationRing.maximalIdeal O).valuation E (r i) =
      WithZero.exp (-(a i)) := fun i => by
    simp only [r, map_mul, map_pow, map_zpow₀, valuation_unif ϖ hϖ, valuation_of_isUnit (hz i), mul_one]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, hab]
    congr 1
    simp
    ring
  have hval : ∀ i, val O (r i) = a i := fun i => by
    simp only [val, hv i, WithZero.log_exp, neg_neg]
  have hrinj : Function.Injective r := fun i j h => by
    have h1 := hval i
    rw [h, hval j] at h1
    exact ha.injective h1.symm
  have hrt : ∀ i, M.charpoly.IsRoot (r i) := fun i => by
    have h1 : ((G.map (algebraMap O E)).charpoly).IsRoot (algebraMap O E (ϖ ^ b i * z i)) := by
      rw [Matrix.charpoly_map]
      exact (hzr i).map
    rw [IsRoot.def, Matrix.eval_charpoly] at h1 ⊢
    have : Matrix.scalar (Fin n) (r i) - M = algebraMap O E ϖ ^ N •
        (Matrix.scalar (Fin n) (algebraMap O E (ϖ ^ b i * z i)) - G.map (algebraMap O E)) := by
      rw [hMG, smul_sub]
      congr 1
      rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      rfl
    rw [this, Matrix.det_smul, h1, mul_zero]
  refine ⟨r, fun i => ⟨hr0 i, hval i⟩, ?_⟩
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) M.charpoly_monic ?_ ?_
  · exact Finset.prod_dvd_of_coprime
      (fun i _ j _ h => pairwise_coprime_X_sub_C hrinj h) fun i _ => dvd_iff_isRoot.2 (hrt i)
  · rw [Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card]
    simp

end GlobalTheory.IwahoriRoots
