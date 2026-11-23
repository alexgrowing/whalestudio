import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionCoefficientsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeOfClosedPoint
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.QCoh GlobalTheory.ChainPts GlobalTheory.ChainPts.PullHT
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transition_coefficients_pullback : ∀ {X X' : Scheme.{0}} (g : X' ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {r : ℕ} (d : Bool) {V V' : X.Opens} {U U' : X'.Opens} (hU : U ≤ g ⁻¹ᵁ V) (hU' : U' ≤ g ⁻¹ᵁ V') {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')} (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r), coef d (isFrame_pullS g hU he) (isFrame_pullS g hU' hs) l i = (g.appLE (V ⊓ V') (U ⊓ U') (inf_le_inf hU hU')).hom (coef d he hs l i) := by
  first | exact @GlobalTheory.ChainPts.PullHT.coef_pulled_frames | exact GlobalTheory.ChainPts.PullHT.coef_pulled_frames | (intros; apply GlobalTheory.ChainPts.PullHT.coef_pulled_frames <;> assumption)
