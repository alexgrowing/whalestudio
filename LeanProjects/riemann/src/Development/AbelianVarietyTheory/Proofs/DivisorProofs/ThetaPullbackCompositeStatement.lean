import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackComposite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pullback_composite : ∀ (S T T' : Scheme.{0}) (P : PPAS S) (f : T ⟶ S) (g : T' ⟶ T), (∃ (Q : PPAS T) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P f ψ ∧ Q.HasTheta) → ∃ (Q : PPAS T') (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (g ≫ f) ψ ∧ Q.HasTheta := by
  first | exact @GlobalTheory.PPAS.isPull_hasTheta_pull | exact GlobalTheory.PPAS.isPull_hasTheta_pull | (intros; apply GlobalTheory.PPAS.isPull_hasTheta_pull <;> assumption)
