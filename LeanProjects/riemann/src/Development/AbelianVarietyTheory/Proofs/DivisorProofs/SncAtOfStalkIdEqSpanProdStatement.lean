import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProd
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)), FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  first | exact @GlobalTheory.sncAt_of_stalkId_eq_span_prod | exact GlobalTheory.sncAt_of_stalkId_eq_span_prod | (intros; apply GlobalTheory.sncAt_of_stalkId_eq_span_prod <;> assumption)
