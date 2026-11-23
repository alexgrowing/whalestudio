import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsStepVecOfIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RouteCompare

noncomputable section

namespace GlobalTheory.FockOrder

variable {D : D7}

theorem exists_sortPerm {n : ℕ} (ε : Fin n → Bool) :
    ∃ π : Equiv.Perm (Fin n), ∀ a, ε (π a) = decide (a.val < (Finset.univ.filter fun a => ε a = true).card) := by
  classical
  set p := (Finset.univ.filter fun a => ε a = true).card with hp
  set q := (Finset.univ.filter fun a => ¬ ε a = true).card with hq
  have hpq : p + q = n := by
    rw [hp, hq, Finset.card_filter_add_card_filter_not]; simp
  have e1 : {a // ε a = true} ≃ Fin p := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  have e2 : {a // ¬ ε a = true} ≃ Fin q := Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])
  refine ⟨(finCongr hpq.symm).trans (finSumFinEquiv.symm.trans ((Equiv.sumCongr e1.symm e2.symm).trans
    (Equiv.sumCompl _))), fun a => ?_⟩
  by_cases ha : a.val < p
  · have h : finCongr hpq.symm a = Fin.castAdd q ⟨a.val, ha⟩ := Fin.ext rfl
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    rw [(e1.symm _).2]; simp [ha]
  · have h : finCongr hpq.symm a = Fin.natAdd p ⟨a.val - p, by omega⟩ := Fin.ext (by simp; omega)
    simp only [Equiv.trans_apply, h, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    have h2 := (e2.symm ⟨a.val - p, by omega⟩).2
    simp only [Bool.not_eq_true] at h2
    rw [h2]; simp [ha]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

end Main

end GlobalTheory.FockOrder

end
