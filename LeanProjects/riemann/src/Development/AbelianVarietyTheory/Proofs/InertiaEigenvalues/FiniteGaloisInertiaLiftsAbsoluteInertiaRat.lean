import Mathlib
import ReciprocityTheory.GaloisValuations.Global

set_option linter.style.haveILetI false

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise

namespace GlobalTheory.InertiaLift

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G F Ω} (hσ : σ ∈ Dec (F := F) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := F) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr ((apply_mem_iff_of_mem_Dec hσ s).mpr
      (mem_of_isIntegral_int A hs))) ?_
    rw [← not_lt, valuation_apply_lt_one_iff hσ, hs1]
    exact lt_irrefl 1
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : σ s * (σ x - x) = (σ t - t) + x * (s - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (σ s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_add_lt _ (h t ht) ?_
    rw [Valuation.map_mul, Valuation.map_sub_swap]
    calc A.valuation x * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) :=
          mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact h s hs
  rwa [Valuation.map_mul, hσs, one_mul] at hv

theorem exists_smul_eq {A A' : ValuationSubring Ω}
    (h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, ∀ y, A'.valuation (g y) < 1 ↔ A.valuation y < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow,
        mem_primeBelow]
      exact h x)
  have e : g • A = A' := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
    rw [primeBelow_smul, hg]
  refine ⟨g, fun y => ?_⟩
  rw [← e, smul_valuation_lt_one_iff]
  have : (g⁻¹ : Ω ≃ₐ[F] Ω) (g y) = y := g.symm_apply_apply y
  rw [this]

noncomputable def intEquiv (s : Ω ≃+* Ω) : IntCl F Ω ≃+* IntCl F Ω where
  toFun b := ⟨s b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_int_of_isIntegral b.2).map s.toRingHom.toIntAlgHom)⟩
  invFun b := ⟨s.symm b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_int_of_isIntegral b.2).map s.symm.toRingHom.toIntAlgHom)⟩
  left_inv b := Subtype.ext (s.symm_apply_apply b)
  right_inv b := Subtype.ext (s.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul s (a : Ω) b)
  map_add' a b := Subtype.ext (map_add s (a : Ω) b)

theorem exists_congr {A : ValuationSubring Ω} (s : Ω ≃+* Ω)
    (hs : ∀ y, A.valuation (s y) < 1 ↔ A.valuation y < 1)
    (h : ∀ x : 𝓞 F, A.valuation (s (algebraMap F Ω x) - algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, g ∈ Dec (F := F) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (g b - s b) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  have hmap : Q = Q.map (intEquiv (F := F) s : IntCl F Ω →+* IntCl F Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow, ← hs ((intEquiv (F := F) s).symm b)]
    have : s (((intEquiv (F := F) s).symm b : IntCl F Ω) : Ω) = b := s.apply_symm_apply b
    rw [this]
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (IntCl F Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intEquiv (F := F) s) hmap) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk Q (intEquiv (F := F) s (algebraMap _ _ x)) =
        Ideal.Quotient.mk Q (algebraMap _ _ x)
      rw [Ideal.Quotient.eq]
      exact h x)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) (Q.under (𝓞 F)) Q φ
  have hσQ' : σ • Q = Q := hσQ
  refine ⟨σ, ?_, fun b hb => ?_⟩
  · refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  · let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    have h1 : Ideal.Quotient.mk Q (σ • b') = Ideal.Quotient.mk Q (intEquiv (F := F) s b') :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b')
    rw [Ideal.Quotient.eq] at h1
    exact h1

omit [IsAlgClosure F Ω] in
theorem mem_Dec_of_lt {A : ValuationSubring Ω} {σ : G F Ω}
    (h : ∀ y, A.valuation (σ y) < 1 ↔ A.valuation y < 1) : σ ∈ Dec (F := F) A := by
  have key : ∀ y, y ∈ A ↔ (y = 0 ∨ ¬ A.valuation y⁻¹ < 1) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
      rw [← A.valuation_le_one_iff, map_inv₀, inv_lt_one₀ h0, not_lt]
      simp [hy]
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, key, key y,
    ← h, map_inv₀ σ, mul_inv_apply, map_eq_zero_iff _ (σ⁻¹ : G F Ω).injective]

theorem exists_mem_Ine_lift (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω]
    [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 → A.valuation ((algebraMap M Ω (τ x)) - (algebraMap M Ω x)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  have hint : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (x : M)) ≤ 1 := fun x =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom))
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x (hint x)
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - (algebraMap M Ω (x : M))) < 1
    rw [h₂]
    exact h x (hint x))
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, mem_Ine_of_integral (mem_Dec_of_lt fun y => ?_)
    fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  intro Ω _ _ _ _ _ A _ M _ _ τ h _
  have hst : @IsScalarTower ℚ M Ω (DivisionRing.toRatAlgebra (R := M)).toSMul
      (inferInstance : Algebra M Ω).toSMul (‹Algebra ℚ Ω›).toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℚ M Ω _ _ _ DivisionRing.toRatAlgebra _ _
      (Subsingleton.elim _ _)
  have e : (DivisionRing.toRatAlgebra : Algebra ℚ M) = M.algebra' := Subsingleton.elim _ _
  have hfd : @FiniteDimensional ℚ M _ _ (DivisionRing.toRatAlgebra (R := M)).toModule := by
    rw [e]; assumption
  exact @exists_mem_Ine_lift ℚ Ω _ _ _ _ _ A M _ DivisionRing.toRatAlgebra _ hst hfd _ τ h

end GlobalTheory.InertiaLift
