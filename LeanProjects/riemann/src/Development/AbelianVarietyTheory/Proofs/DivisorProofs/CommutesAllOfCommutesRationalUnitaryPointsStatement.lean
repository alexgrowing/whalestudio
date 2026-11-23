import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesAllOfCommutesRationalUnitaryPoints
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutes_all_of_commutes_rationalUnitaryPoints : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)),
    (∀ τ, D.what₂.embLL.comp (tauL τ) = Formalism.BasicNotions.TH.tauE D τ) →
    ∀ (lam : D.what₂.Tau → DomWeight V.rank) (g : Module.End D.what₂.LL (VV D.what₂.LL lam)),
    (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, g (rhoVr tauL lam γE v) = rhoVr tauL lam γE (g v)) →
    ∀ (h : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL) v, g (rhoK lam h v) = rhoK lam h (g v) := by
  first | exact @GlobalTheory.RatDenseEnd.comm_all | exact GlobalTheory.RatDenseEnd.comm_all | (intros; apply GlobalTheory.RatDenseEnd.comm_all <;> assumption)
