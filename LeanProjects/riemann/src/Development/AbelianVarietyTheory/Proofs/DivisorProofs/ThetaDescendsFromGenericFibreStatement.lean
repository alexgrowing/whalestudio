import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_descends_from_generic_fibre : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsRegSurf q → ∀ P : PPAS Y, (∃ (Q : PPAS (Sp Y.functionField)) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (Y.fromSpecStalk (genericPoint Y)) ψ ∧ Q.HasTheta) → P.HasTheta := by
  first | exact @GlobalTheory.ThetaExtend.hasTheta_of_regSurf | exact GlobalTheory.ThetaExtend.hasTheta_of_regSurf | (intros; apply GlobalTheory.ThetaExtend.hasTheta_of_regSurf <;> assumption)
