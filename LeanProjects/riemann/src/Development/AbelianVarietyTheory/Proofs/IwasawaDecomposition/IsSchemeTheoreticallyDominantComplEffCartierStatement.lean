import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier : ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I → IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  first | exact @GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | exact GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier | (intros; apply GlobalTheory.ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier <;> assumption)
