import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeCmEqIdealAndCovolume

open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane

noncomputable section

namespace GlobalTheory

namespace CMCurves

private theorem c4_pow_three_eq_j_mul_discr {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    W.c₄ ^ 3 = W.j * W.Δ := by
  rw [WeierstrassCurve.j, ← W.coe_Δ', mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

theorem exists_integral_curve {j : ℂ} (hj : IsIntegral ℤ j) :
    ∃ E : WeierstrassCurve ℂ, IsIntegral ℤ E.a₁ ∧ IsIntegral ℤ E.a₂ ∧ IsIntegral ℤ E.a₃ ∧
      IsIntegral ℤ E.a₄ ∧ IsIntegral ℤ E.a₆ ∧ E.Δ = 1 ∧ E.c₄ ^ 3 = j := by
  classical
  have hjQ : IsIntegral ℚ j := hj.tower_top
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {j}
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hjQ
  have : NumberField K := ⟨⟩
  let jK : K := ⟨j, IntermediateField.mem_adjoin_simple_self ℚ j⟩
  have hWj : (WeierstrassCurve.ofJ jK).j = jK := WeierstrassCurve.ofJ_j jK
  have hjK : IsIntegral ℤ (WeierstrassCurve.ofJ jK).j := by
    rw [hWj]
    exact (isIntegral_algHom_iff ((K.val : K →+* ℂ).toIntAlgHom) Subtype.val_injective).1 hj
  obtain ⟨M, hNF, -, C, W₀, hW, hΔ⟩ := exists_finite_model_ringOfIntegers (WeierstrassCurve.ofJ jK) hjK
  have := hNF
  let ψ : M →ₐ[K] ℂ := (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] ℂ).comp M.val
  have : ((WeierstrassCurve.ofJ jK).baseChange M).IsElliptic :=
    ⟨by rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
        exact (WeierstrassCurve.isUnit_Δ _).map _⟩
  have : W₀.IsElliptic := ⟨by rw [hΔ]; exact isUnit_one⟩
  have hint : ∀ x : 𝓞 M, IsIntegral ℤ (ψ (x : M)) := fun x =>
    x.isIntegral_coe.map (ψ : M →+* ℂ).toIntAlgHom
  have h1 : (C • (WeierstrassCurve.ofJ jK).baseChange M).j = algebraMap K M jK := by
    rw [WeierstrassCurve.variableChange_j]
    erw [WeierstrassCurve.map_j, hWj]
  have h2 := c4_pow_three_eq_j_mul_discr (C • (WeierstrassCurve.ofJ jK).baseChange M)
  rw [h1, hW] at h2
  have hB : (W₀.baseChange M).Δ = 1 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ, map_one]
  refine ⟨(W₀.baseChange M).map (ψ : M →+* ℂ), hint _, hint _, hint _, hint _, hint _, ?_, ?_⟩
  · rw [WeierstrassCurve.map_Δ, hB, map_one]
  · rw [WeierstrassCurve.map_c₄, ← map_pow, h2, hB, mul_one]
    show ψ (algebraMap K M jK) = j
    rw [AlgHom.commutes]
    rfl

def latticeJ (L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

theorem latticeJ_eq_of_isHomothetic {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeJ L' = latticeJ L := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact L.ω₁_div_two_notMem_lattice ((h _).1 (by simp))
  have hd := g₂_cube_sub_g₃_sq_ne_zero L
  have hd' := g₂_cube_sub_g₃_sq_ne_zero L'
  unfold latticeJ
  rw [h.g₂_eq, h.g₃_eq] at hd' ⊢
  rw [div_eq_div_iff hd' hd]
  ring

variable {K : Type} [Field K] [NumberField K]

private theorem exists_ne_zero_upperHalfPlane_lattice_eq (L : PeriodPair) : ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧
    ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  have hind := LinearIndependent.pair_iff.1 L.indep
  have h1 : L.ω₁ ≠ 0 := fun h => by simpa using hind 1 0 (by simp [h])
  have h2 : L.ω₂ ≠ 0 := fun h => by simpa using hind 0 1 (by simp [h])
  have him : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro h
    have hr : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
      rw [← div_eq_iff h1]; exact Complex.ext (by simp) (by simp [h])
    have := hind (-(L.ω₂ / L.ω₁).re) 1 (by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; linear_combination hr)
    exact one_ne_zero this.2
  rcases lt_or_gt_of_ne him with hlt | hgt
  · have hpos : 0 < (L.ω₁ / L.ω₂).im := by
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.2 hlt) (Complex.normSq_pos.2 (div_ne_zero h2 h1))
    refine ⟨L.ω₂, UpperHalfPlane.mk _ hpos, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice, UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by field_simp⟩
  · refine ⟨L.ω₁, UpperHalfPlane.mk _ hgt, h1, fun x => ?_⟩
    rw [PeriodPair.mem_lattice, UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨n, m, by field_simp; ring⟩
    · rintro ⟨m, n, rfl⟩; exact ⟨n, m, by field_simp; ring⟩

theorem isIntegral_latticeJ (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (L : PeriodPair)
    (hL : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) :
    IsIntegral ℤ (latticeJ L) := by
  obtain ⟨a, τ, ha, h⟩ := exists_ne_zero_upperHalfPlane_lattice_eq L
  rw [show latticeJ L = modularJ τ from g₂_cube_div_eq_modularJ ha h]
  have key : ∀ y, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := by
    intro y
    rw [Submodule.mem_span_pair, h]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by simp [zsmul_eq_mul]⟩
    · rintro ⟨m, n, e⟩
      exact ⟨m, n, by simpa [zsmul_eq_mul] using mul_left_cancel₀ ha e⟩
  refine isIntegral_modularJ_of_ringOfIntegers hK σ (fun α x hx => ?_)
  rw [key] at hx ⊢
  simpa [mul_left_comm] using hL α _ hx

theorem latticeJ_eq_of_class_eq (σ : K →+* ℂ) {L L' : PeriodPair} {𝔞 𝔞' : (Ideal (𝓞 K))⁰}
    {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K))
    (h' : ∀ z, z ∈ L'.lattice ↔ ∃ a ∈ (𝔞' : Ideal (𝓞 K)), z = c' * σ (a : K))
    (e : ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔞') : latticeJ L' = latticeJ L := by
  obtain ⟨x, y, hx, hy, he⟩ := ClassGroup.mk0_eq_mk0_iff.1 e
  have hxK : σ (x : K) ≠ 0 := (map_ne_zero σ).2 (by exact_mod_cast hx)
  have hyK : σ (y : K) ≠ 0 := (map_ne_zero σ).2 (by exact_mod_cast hy)
  have hk : IsHomothetic (c' * σ (x : K) / (c * σ (y : K))) L L' := by
    intro w
    rw [h', h]
    constructor
    · rintro ⟨a', ha', hw⟩
      have hm : y * a' ∈ Ideal.span {x} * (𝔞 : Ideal (𝓞 K)) := by
        rw [he]; exact Ideal.mem_span_singleton_mul.2 ⟨a', ha', rfl⟩
      obtain ⟨a, ha, hxa⟩ := Ideal.mem_span_singleton_mul.1 hm
      refine ⟨a, ha, ?_⟩
      have hs : σ (x : K) * σ (a : K) = σ (y : K) * σ (a' : K) := by
        simpa using congrArg (fun t : 𝓞 K => σ (t : K)) hxa
      apply mul_left_cancel₀ (mul_ne_zero hc' hxK)
      have hw' : c' * σ (x : K) * w = c * σ (y : K) * (c' * σ (a' : K)) := by
        rw [← hw]; field_simp
      linear_combination hw' - c * c' * hs
    · rintro ⟨a, ha, rfl⟩
      have hm : x * a ∈ Ideal.span {y} * (𝔞' : Ideal (𝓞 K)) := by
        rw [← he]; exact Ideal.mem_span_singleton_mul.2 ⟨a, ha, rfl⟩
      obtain ⟨a', ha', hxa⟩ := Ideal.mem_span_singleton_mul.1 hm
      refine ⟨a', ha', ?_⟩
      have hs : σ (y : K) * σ (a' : K) = σ (x : K) * σ (a : K) := by
        simpa using congrArg (fun t : 𝓞 K => σ (t : K)) hxa
      rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hc hyK)]
      linear_combination (-(c * c')) * hs
  exact latticeJ_eq_of_isHomothetic hk

theorem finite_latticeJ (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    (latticeJ '' {L | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}).Finite := by
  classical
  set S := latticeJ '' {L : PeriodPair | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}
  have key : ∀ j : S, ∃ (𝔞 : (Ideal (𝓞 K))⁰) (L : PeriodPair) (c : ℂ), c ≠ 0 ∧
      latticeJ L = j ∧ ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K) := by
    rintro ⟨_, L, hL, rfl⟩
    obtain ⟨𝔞, c, h𝔞, hc, h⟩ := CMLattice.exists_ideal σ hσ L hL
    exact ⟨⟨𝔞, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩, L, c, hc, rfl, h⟩
  choose f L c hc hLj hL using key
  have inj : Function.Injective (fun j : S => ClassGroup.mk0 (f j)) := by
    intro j j' hjj
    apply Subtype.ext
    rw [← hLj j, ← hLj j']
    exact latticeJ_eq_of_class_eq σ (hc j') (hc j) (hL j') (hL j) hjj.symm
  have : Finite S := Finite.of_injective _ inj
  exact Set.toFinite S

end CMCurves

open CMCurves in

theorem exists_field_cm_curves_unit_discriminant :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ : K →+* ℂ),
    ¬ NumberField.ComplexEmbedding.IsReal σ →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ L : PeriodPair, (∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) →
        ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
          (((W.c₄ : M) : ℂ)) ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
            1728 * L.g₂ ^ 3 * ((W.Δ : M) : ℂ) := by
  intro K _ _ hK σ hσ
  classical
  set S := latticeJ '' {L : PeriodPair | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}
  have hS : S.Finite := finite_latticeJ σ hσ
  have hcurve : ∀ j : S, ∃ E : WeierstrassCurve ℂ, IsIntegral ℤ E.a₁ ∧ IsIntegral ℤ E.a₂ ∧
      IsIntegral ℤ E.a₃ ∧ IsIntegral ℤ E.a₄ ∧ IsIntegral ℤ E.a₆ ∧ E.Δ = 1 ∧ E.c₄ ^ 3 = j := by
    rintro ⟨_, L, hL, rfl⟩
    exact exists_integral_curve (isIntegral_latticeJ hK σ L hL)
  choose E hE using hcurve
  have : Finite S := hS.to_subtype
  let T : Set ℂ := ⋃ j : S, {(E j).a₁, (E j).a₂, (E j).a₃, (E j).a₄, (E j).a₆}
  have : Finite T := (Set.finite_iUnion fun j => Set.toFinite _).to_subtype
  have hTint : ∀ z ∈ T, IsIntegral ℤ z := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz
    obtain ⟨h1, h2, h3, h4, h6, -⟩ := hE j
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> assumption
  let σ' : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
  have : FiniteDimensional ℚ σ'.fieldRange :=
    (AlgEquiv.ofInjectiveField σ').toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hTint z hz).tower_top
  let M : IntermediateField ℚ ℂ := σ'.fieldRange ⊔ IntermediateField.adjoin ℚ T
  have hTM : ∀ z ∈ T, z ∈ M := fun z hz =>
    (le_sup_right : IntermediateField.adjoin ℚ T ≤ M) (IntermediateField.subset_adjoin ℚ T hz)
  refine ⟨M, inferInstance, fun a => (le_sup_left : σ'.fieldRange ≤ M) ⟨a, rfl⟩, fun L hL => ?_⟩
  let j : S := ⟨latticeJ L, L, hL, rfl⟩
  obtain ⟨h1, h2, h3, h4, h6, hΔ, hc4⟩ := hE j
  have mk : ∀ z ∈ T, IsIntegral ℤ z → ∃ t : 𝓞 M, ((t : M) : ℂ) = z := fun z hz hi =>
    ⟨⟨⟨z, hTM z hz⟩, (isIntegral_algHom_iff ((M.val : M →+* ℂ).toIntAlgHom)
      Subtype.val_injective).1 hi⟩, rfl⟩
  have hmem : ∀ z ∈ ({(E j).a₁, (E j).a₂, (E j).a₃, (E j).a₄, (E j).a₆} : Set ℂ), z ∈ T :=
    fun z hz => Set.mem_iUnion.2 ⟨j, hz⟩
  obtain ⟨t1, ht1⟩ := mk _ (hmem _ (by simp)) h1
  obtain ⟨t2, ht2⟩ := mk _ (hmem _ (by simp)) h2
  obtain ⟨t3, ht3⟩ := mk _ (hmem _ (by simp)) h3
  obtain ⟨t4, ht4⟩ := mk _ (hmem _ (by simp)) h4
  obtain ⟨t6, ht6⟩ := mk _ (hmem _ (by simp)) h6
  let W : WeierstrassCurve (𝓞 M) := ⟨t1, t2, t3, t4, t6⟩
  let φ : 𝓞 M →+* ℂ := (M.val : M →+* ℂ).comp (algebraMap (𝓞 M) M)
  have hφ : Function.Injective φ :=
    Subtype.val_injective.comp RingOfIntegers.coe_injective
  have hWE : W.map φ = E j := by
    ext
    · exact ht1
    · exact ht2
    · exact ht3
    · exact ht4
    · exact ht6
  have hWΔ : W.Δ = 1 := hφ (by rw [← WeierstrassCurve.map_Δ, hWE, hΔ, map_one])
  have hWc : ((W.c₄ : M) : ℂ) = (E j).c₄ := by
    rw [← hWE, WeierstrassCurve.map_c₄]; rfl
  refine ⟨W, hWΔ ▸ isUnit_one, ?_⟩
  rw [hWc, hc4, hWΔ]
  have hd := g₂_cube_sub_g₃_sq_ne_zero L
  show latticeJ L * _ = _
  unfold latticeJ
  field_simp
  simp

end GlobalTheory
