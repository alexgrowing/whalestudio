import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBottChernMeasure
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_bott_chern_measure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (S : ShortComplex X.Modules) (hS : S.ShortExact) (r s : ℕ) (g : VMetric p S.X₂ (r + s)) (G : g.IsCInf) (hi : VB.IsSubbundle S.f) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) (σ : k →+* ℂ), (g.met σ).bcMeas hS h₁ h₃ univ ≠ ⊤ → (h.atlas σ).integral (bcFld (h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ)) = ((g.met σ).bcMeas hS h₁ h₃ univ).toReal := by
  first | exact @GlobalTheory.BcUnique.integral_bcFld_seq | exact GlobalTheory.BcUnique.integral_bcFld_seq | (intros; apply GlobalTheory.BcUnique.integral_bcFld_seq <;> assumption)
