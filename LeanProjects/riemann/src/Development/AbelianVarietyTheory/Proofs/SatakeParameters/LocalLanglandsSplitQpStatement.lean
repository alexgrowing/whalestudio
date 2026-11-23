import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_split_qp : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : GlobalTheory.NPin.Pin hL D) (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (k : Fin 2) (w : PlE D.host) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w), (∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n), Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) → P.T.e w (rcw n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) → D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)))) := by
  first | exact @GlobalTheory.SerChar.locG_muC_eq_rcw | exact GlobalTheory.SerChar.locG_muC_eq_rcw | (intros; apply GlobalTheory.SerChar.locG_muC_eq_rcw <;> assumption)
