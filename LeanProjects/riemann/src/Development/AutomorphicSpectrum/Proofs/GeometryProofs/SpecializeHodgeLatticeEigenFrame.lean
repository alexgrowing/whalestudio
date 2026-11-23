import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj

theorem ev_eigProj : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g ℓ ψ ρH ρHC HL ev σ σC h hp hev htie hst
  choose hc hψ using htie
  have hsum : (⟨_, hp⟩ : HL) = ∑ k, (⟨σ (HT.dualInt E k), hc _⟩ : R') •
      (⟨ρH (RingOfIntegers.basis E k) (h : Vs × Module.Dual Ω Vs), hst _ _ h.2⟩ : HL) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  rw [hsum, map_sum]
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, hψ, hev.1 _ h]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj
