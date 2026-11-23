import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder

namespace GlobalTheory.BcUnique

theorem isInduced_seq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (S : ShortComplex X.Modules) (hS : S.ShortExact) (r s : ℕ) (g : VMetric p S.X₂ (r + s)) (G : g.IsCInf) (hi : VB.IsSubbundle S.f) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) (σ : k →+* ℂ), IsInduced (h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ) := by
  intro k _ X p h S hS r s g G hi h₁ h₃ σ a y hy
  refine ⟨?_, ?_⟩
  · ext i j
    rfl
  · exact (g.met σ).quot_G hS h₁ h₃ a hy

end GlobalTheory.BcUnique
