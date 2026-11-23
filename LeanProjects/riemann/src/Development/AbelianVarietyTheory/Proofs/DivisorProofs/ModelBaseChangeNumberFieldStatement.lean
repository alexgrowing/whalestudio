import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelBaseChangeNumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_base_change_number_field : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {F : Type} [Field F] [NumberField F]
    (e : F ≃+* c.F) {V : Scheme.{0}} [IsIntegral V] (j : V ⟶ gen Z), IsClosedImmersion j → ∀ {d : ℕ},
    topologicalKrullDim V = d →
    ∃ (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ gen Z) (ρ : X ⟶ Z.X),
      IsPre (genStr Z ≫ spMap e.toRingHom) (Set.range j) d (genι Z) q jB πB ρ ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∀ (τ : E →+* ℂ) (x : X),
        (∃ (U : X.Opens) (u : LocAssign Z (Dw.mult τ) jB U), x ∈ U ∧ IsAffineOpen U ∧
          IsLocFrame Z e jB πB _ τ U u ∧ IsLocLat Z e jB πB _ τ (ArIn.ind ∅) U u) ∧
        ∃ (U : X.Opens) (u : LocAssign Z (Dw.mult τ) jB U), x ∈ U ∧ IsAffineOpen U ∧
          IsLocFrame Z e jB πB _ τ U u ∧ GlobalTheory.TwoLat.IsLocGrLat Z e jB πB _ τ U u := by
  first | exact @GlobalTheory.TwoLat.exists_base_deRham | exact GlobalTheory.TwoLat.exists_base_deRham | (intros; apply GlobalTheory.TwoLat.exists_base_deRham <;> assumption)
