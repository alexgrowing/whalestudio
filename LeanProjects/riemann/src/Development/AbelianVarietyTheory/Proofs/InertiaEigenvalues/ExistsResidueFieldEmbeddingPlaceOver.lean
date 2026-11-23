import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem GlobalTheory.residue_ringOfIntegers_to_place : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g),
    ∃ ι : 𝓞 E' ⧸ w'.asIdeal →+* Formalism.CyclotomicNorms.Fbar g,
      ∀ x : 𝓞 E', ι (Ideal.Quotient.mk _ x) = redThrough A κ (algebraMap E' Ω (x : E')) := by
  intro E' Ω _ _ _ _ g _ A w' h' κ
  classical
  have hmem : ∀ x : 𝓞 E', algebraMap E' Ω (x : E') ∈ A := by
    intro x
    have hi : IsIntegral ℤ (algebraMap E' Ω (x : E')) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E' Ω)
    have h2 : IsIntegral A.valuation.integer (algebraMap E' Ω (x : E')) := hi.tower_top
    have h3 := (Valuation.integer.integers A.valuation).mem_of_integral h2
    obtain ⟨y, hy⟩ := h3
    rw [← hy]
    exact (A.valuation_le_one_iff _).1 (by simpa [Algebra.smul_def] using y.2)
  let φ : 𝓞 E' →+* A :=
    { toFun := fun x => ⟨algebraMap E' Ω (x : E'), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let ψ : 𝓞 E' →+* Formalism.CyclotomicNorms.Fbar g := κ.toRingHom.comp ((IsLocalRing.residue A).comp φ)
  have hker : ∀ x ∈ w'.asIdeal, ψ x = 0 := by
    intro x hx
    have hlt : A.valuation (algebraMap E' Ω (x : E')) < 1 := (h' x).2 hx
    have hm : φ x ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff (φ x)).2 hlt
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [(IsLocalRing.residue_eq_zero_iff (φ x)).2 hm, map_zero]
  refine ⟨Ideal.Quotient.lift _ ψ hker, fun x => ?_⟩
  rw [Ideal.Quotient.lift_mk]
  unfold redThrough
  rw [dif_pos (hmem x)]
  rfl
