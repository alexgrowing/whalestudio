import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfNatCastEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ z₁ : M₁.Z, letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ (𝔷 : Ideal (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)), 𝔷.IsMaximal → ∀ z₂ : M₂.Z, q z₂ = z₁ → (∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M₂.Z), q (y (cPt p)) = z₁ → (∀ b ∈ 𝔷, ‖M₂.val (gPt p ≫ y) (b : Ω₂)‖ < 1) → y (cPt p) = z₂ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hN hF hg z₁
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 z₂ hz₂ hmem p _ y hy hsmall
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN hF hg z₁
  have hO : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b : Ω₂) ∈ M₂.O (y (cPt p)) :=
    fun b => (h1 b).1 b.2 _ hy
  let ι : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.O (y (cPt p)) :=
    (RingHom.id Ω₂).restrict _ _ fun c hc => hO ⟨c, hc⟩
  have hle : 𝔷 ≤ (IsLocalRing.maximalIdeal (M₂.O (y (cPt p)))).comap ι := by
    intro b hb
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (RatModel.norm_val_lt_one_iff rfl (hO b)).1 (hsmall b hb)
  have heq := h𝔷.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hle
  have key : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂) ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O (y (cPt p))) := by
    intro b
    rw [← hmem b, heq, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, RatModel.isUnit_O_iff]
    show ¬ ((b : Ω₂) ≠ 0 ∧ (b : Ω₂)⁻¹ ∈ M₂.O (y (cPt p))) ↔ _
    tauto
  refine (h3 z₂ (y (cPt p)) hz₂ hy fun b => ?_).symm
  by_cases hb0 : (b : Ω₂) = 0
  · rw [hb0, inv_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · have := key b
    simp only [hb0, false_or] at this
    exact not_iff_not.1 this
