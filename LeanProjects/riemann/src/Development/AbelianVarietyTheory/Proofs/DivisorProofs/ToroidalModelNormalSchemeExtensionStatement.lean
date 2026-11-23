import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelNormalSchemeExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_model_normal_scheme_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {X : Scheme.{0}} [IsIntegral X],
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ (U : X.Opens) [Nonempty U], CharZero Γ(X, U)) → ∀ (ρ : X ⟶ Z.X),
    GlobalTheory.HtGen.SplitK Z.t (K := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ ρ) 1 → ∀ (x : X) (τ : E →+* ℂ),
    ∃ V : X.affineOpens, x ∈ V.1 ∧ ∃ (n m : ℕ) (A : Fin m → Γ(X, V.1)), n ≠ 0 ∧
      (n : Γ(X, V.1)) ∈ (Ideal.span (Set.range A)).radical ∧
      ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : Γ(X, V.1) →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) →
        GlobalTheory.TwoLat.GrBasis Z (spMap ψ ≫ V.2.fromSpec ≫ ρ) τ (Dw.mult τ) := by
  first | exact @GlobalTheory.TwoLat.exists_grChart | exact GlobalTheory.TwoLat.exists_grChart | (intros; apply GlobalTheory.TwoLat.exists_grChart <;> assumption)
