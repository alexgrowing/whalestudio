import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.TopLevelInv

theorem det_kapAt_val {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (mt (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).det) := by
  unfold kapAt GlobalTheory.FunObj.inBasis
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.SplitFlip.gdet, GlobalTheory.StepData.det_reGL]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  obtain ⟨X, hX⟩ : ∃ X, X = (MulAut.conj (S.βp (j + 1))⁻¹) ((finG (G.V (.top (j + 1)))) k) := ⟨_, rfl⟩
  rw [← hX]
  refine ((RingHom.map_det (StdFrames.cpt w) X.val).symm : _).trans (congrArg _ ?_)
  rw [hX, MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul, inv_inv, mul_right_comm, ← det_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul]
  show ((Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1))))).val).det = _
  rw [GlobalTheory.VecInv.finE_val, RingHom.map_det]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem detAt_conjPt_eq_prod {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} (_ht : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1)))
    (e : AE D) (hI : IsIdemSum e (locPl G t)) :
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  classical
  have he2 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI).idem
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hI
  have hcomp : ∀ Q, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = if Q ∈ locPl G t then 1 else 0 := by
    intro Q
    obtain ⟨⟨es, hes, hsum⟩, -⟩ := hI
    rw [hsum, map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) Q)]
    split_ifs with hQ
    · rw [Finset.sum_eq_single Q (fun P hP hPQ => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
        (fun h => absurd hQ h)]
      exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
    · exact Finset.sum_eq_zero fun P hP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))
  have hloc : ∀ (w Q : Pl D.host.E) (y : (Kw w)ˣ),
      GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
        (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
    intro w Q y
    rw [GlobalTheory.DepthFix.cpt_eq_finAd]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)
  have hdet : (mt (G.V (.top (j + 1))) (conjPt S j k)).det = (mt (G.V (.top (j + 1))) (k : GA D _)).det := by
    unfold Formalism.L2.Theta.mt
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [mul_right_comm, inv_mul_cancel, one_mul]
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Units.coe_prod, hdet]
  apply GlobalTheory.FunObj.ae_ext
  · rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero, map_prod]
    exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) w.1 _).symm
  · intro Q
    simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, map_prod, hcomp, hloc]
    by_cases hQ : Q ∈ locPl G t
    · rw [if_pos hQ, one_mul, sub_self, add_zero, Finset.prod_eq_single ⟨Q, hQ⟩]
      · rw [GlobalTheory.LFun.finSingle_self, det_kapAt_val]
      · intro b _ hb
        exact GlobalTheory.LFun.finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hQ, zero_mul, zero_add, sub_zero]
      exact (Finset.prod_eq_one fun w _ => GlobalTheory.LFun.finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _).symm

end GlobalTheory.TopLevelInv
