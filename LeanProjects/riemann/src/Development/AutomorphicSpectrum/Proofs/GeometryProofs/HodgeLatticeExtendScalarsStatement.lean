import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalars
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_extend_scalars : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs)) (bar : 𝓞 E ≃+* 𝓞 E)
    (R R' : Subring Ω) (hR : R ≤ R') (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HLx : Submodule R (Vs × Module.Dual Ω Vs)) (HLy : Submodule R' (Vs × Module.Dual Ω Vs))
    (C A : Type) [Field C] [CommRing A] [Algebra A C] (ψ : R' →+* C),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    HodgeAt ρH HLx ℓ t → HodgeAt ρH HLy ℓ t →
    (∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) →
    ∃ (ρC : 𝓞 E →+* Module.End C (Fin g → C))
      (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
      (ev : HLy →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
      (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C))),
      (∀ a y, (ρHC a y).1 = ρC a y.1) ∧ (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) ∧
      Tied ℓ ψ ρ ρC ∧ IsEval ℓ ψ ρH ρHC HLy ev ∧
      HV.map ((LinearMap.fst C (Fin g → C) (Module.Dual C (Fin g → C))).restrictScalars A) = stdLat A C g ∧
      (∀ f : Module.Dual C (Fin g → C), ((0 : Fin g → C), f) ∈ HV ↔
        ∀ e ∈ stdLat A C g, f e ∈ (algebraMap A C).range) ∧
      ∀ ht : ∀ i, t i ∈ HLy, HT.IsFreeOn ρHC HV (fun i => ev ⟨t i, ht i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval <;> assumption)
