import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatrices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KapLatSupp

theorem mxAt_embed_kappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S T A : HSp D) (o : OrthDec T A L') (P : Pl D → Prop) (x : WO S L'), MxAt P x → MxAt P ((B.o.resS S).symm (0, l.κ S x)) ∧ MxAt P ((o.resT S).symm (0, x)) := by
  intro D ρ B L' ζ' l S T A o P x hx
  refine ⟨?_, ?_⟩
  · rw [OrthDec.resS_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_r GlobalTheory.LastOpPf.mxAt_zero _)
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LinkKapMx.mxAt_linkKappa D ρ B L' ζ' l S P x hx) _)
  · rw [OrthDec.resT_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_l _ GlobalTheory.LastOpPf.mxAt_zero) (GlobalTheory.LastOpPf.mxAt_mul_l _ hx)

end GlobalTheory.KapLatSupp
