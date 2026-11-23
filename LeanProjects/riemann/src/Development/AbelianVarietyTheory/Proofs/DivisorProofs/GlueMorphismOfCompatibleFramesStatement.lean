import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismOfCompatibleFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_morphism_of_compatible_frames : ∀ (X : Scheme.{0}) (M M' : X.Modules) (r : ℕ) (ι : Type) (U : ι → X.Opens), (∀ x : X, ∃ i, x ∈ U i) →
    ∀ (f : ∀ i, Fin r → Γ(M, U i)) (hf : ∀ i, VB.IsFrame (f i)) (φ : ∀ i, Fin r → Γ(M', U i)),
    (∀ i j a, Twist.resM M' (inf_le_right : U i ⊓ U j ≤ U j) (φ j a) =
      ∑ b, trCo (hf i) (f j) b a • Twist.resM M' (inf_le_left : U i ⊓ U j ≤ U i) (φ i b)) →
    ∃ g : M ⟶ M', ∀ i a, g.app (U i) (f i a) = φ i a := by
  first | exact @GlobalTheory.FrameGlue.exists_hom_of_frames | exact GlobalTheory.FrameGlue.exists_hom_of_frames | (intros; apply GlobalTheory.FrameGlue.exists_hom_of_frames <;> assumption)
