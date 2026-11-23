import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeEigenDecompositionLocal
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
theorem _root_.GlobalTheory.T.hodge_lattice_eigen_decomposition_local : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (bar : 𝓞 E ≃+* 𝓞 E) (R' : Subring Ω) [IsLocalRing R'] (g p q : ℕ) (ℓ : Fin g → Vs)
    (t : Fin (p + q) → Vs × Module.Dual Ω Vs) (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (σ σ' : E →+* Ω),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ e, σ e ∈ R') → (∀ e, σ' e ∈ R') →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ → HodgeAt ρH HL ℓ t →
    Module.finrank Ω (HT.eigSp ρ σ) = p → Module.finrank Ω (HT.eigSp ρ σ') = q →
    ∃ (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
      (A : Matrix (Fin (p + q)) (Fin (p + q)) R'),
      LinearIndependent Ω b₁ ∧ Submodule.span R' (Set.range b₁) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) ∧
      LinearIndependent Ω b₂ ∧ Submodule.span R' (Set.range b₂) = HT.eigSub ρ σ' (Submodule.span R' (Set.range ℓ)) ∧
      IsAdapted ρH σ b₁ b₂ u ∧ (∀ i, u i ∈ HL) ∧ IsUnit A.det ∧
      ∀ i, HT.eigProj ρH σ (t i) = ∑ j, (A i j : Ω) • u j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames <;> assumption)
