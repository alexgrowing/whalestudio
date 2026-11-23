import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O) (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  first | (exact @GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (exact GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (intros; apply GlobalTheory.UPel.HT.siegPre_actPB_pullback  <;> assumption)
