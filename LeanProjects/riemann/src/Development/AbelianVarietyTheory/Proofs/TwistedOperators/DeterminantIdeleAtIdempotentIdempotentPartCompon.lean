import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section

namespace GlobalTheory.TopLevelInv

variable {D : D7}

theorem infPart_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum (infPart D).toAddMonoidHom es P
  change (infPart D).toAddMonoidHom _ = 0
  rw [hs]
  exact Finset.sum_eq_zero fun PP hPP =>
    (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) (hes PP hPP)).1

open Classical in

theorem cpt_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom es P
  change ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom _ = _
  rw [hs]
  have h : ∀ PP ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (es PP)) = if PP = Q then 1 else 0 := fun PP hPP => by
    by_cases hQ : PP = Q
    · subst hQ; rw [if_pos rfl]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · rw [if_neg hQ]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 Q (Ne.symm hQ)
  calc _ = ∑ PP ∈ P, (if PP = Q then (1 : Q.adicCompletion D.host.E) else 0) := Finset.sum_congr rfl h
    _ = _ := by rw [Finset.sum_ite_eq']

theorem cpt_one_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∈ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 1 := by
  classical
  rw [cpt_of_isIdemSum he, if_pos hQ]

theorem cpt_zero_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∉ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 0 := by
  classical
  rw [cpt_of_isIdemSum he, if_neg hQ]

theorem map_unitMix_of_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (e x : R) (h : φ e = 0) :
    φ (e * x + (1 - e)) = 1 := by
  rw [map_add, map_mul, map_sub, map_one, h]; ring

set_option maxHeartbeats 1000000 in
theorem detAt_cutPart_parts {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧
    (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧
    ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hc
  have hval : (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g) : AE D) =
      e * (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det + (1 - e) := rfl
  rw [hval]
  have hinf := infPart_of_isIdemSum he
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 1 := cpt_one_of_isIdemSum he hQ
    have h2 : φ (cA D e) = 0 := by
      have := congrArg φ hc
      rwa [RingHom.map_mul, RingHom.map_zero, h1, one_mul] at this
    have h3 : φ (e + cA D e) = 1 := by rw [RingHom.map_add, h1, h2, add_zero]
    change φ _ = ((Formalism.L2.Theta.mt V g).map φ).det
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h1, one_mul, sub_self, add_zero,
      RingHom.map_det, mt_cutPart hf.1 hf.2]
    congr 1
    refine Matrix.ext fun i j => ?_
    change φ ((e + cA D e) * Formalism.L2.Theta.mt V g i j + (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j) = φ (Formalism.L2.Theta.mt V g i j)
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h3, one_mul, sub_self,
      zero_mul, add_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 0 := cpt_zero_of_isIdemSum he hQ
    change φ _ = 1
    exact map_unitMix_of_zero φ e _ h1

end GlobalTheory.TopLevelInv

end
