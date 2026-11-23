import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

variable {D : D7} {v : Pl D.host.F}

def evW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Lev.EAf D →+* Fv D.host.F v :=
  (complEquiv τ (splitPrime_under τ)).symm.toRingHom.comp (cpt (D := D) (splitPrime τ))

theorem complEquiv_evW (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    complEquiv τ (splitPrime_under τ) (evW τ z) = cpt (D := D) (splitPrime τ) z := by
  exact (complEquiv τ (splitPrime_under τ)).apply_symm_apply _

theorem evW_toEAf (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) : evW τ (toEAf D a) = piW τ a := by
  apply (complEquiv τ (splitPrime_under τ)).injective
  rw [complEquiv_evW]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [FlipMatch.cpt_tmul, FlipMatch.piW_tmul, map_mul, complEquiv_apply, complEquiv_apply,
      complMap_apply_emb, mul_comm]
    congr 1
    rw [← FlipMatch.complMap_apply_under (splitPrime_under τ)]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]

end GlobalTheory.BotMatch

end
