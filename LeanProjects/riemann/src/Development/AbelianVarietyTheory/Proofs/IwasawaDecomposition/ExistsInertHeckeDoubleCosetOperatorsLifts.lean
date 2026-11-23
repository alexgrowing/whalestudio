import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslatesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.InertTie

theorem conj_symm_apply {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (e : M ≃ₗ[K] N) (T : Module.End K M) (x : N) : e.symm (e.conj T x) = T (e.symm x) := by
  simp [LinearEquiv.conj_apply]

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X))
    (P : LiftBrg.PresL X I hX U Xg tr L cV i t) (hP : LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf (Vc X.toD7 i)))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.toD7.host.E X.B.R.nV ∅ (LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e)
    (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeLI i t q f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
        ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  funext g
  rw [hP]
  unfold Bridge.dcOp
  rw [Finset.sum_congr rfl (fun a _ => hP f (g * a))]
  rw [hN _ (fun e => P.coef ((((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f).1 e)) g]
  refine (congrArg P.coef ?_).trans (map_sum P.coef _ _)
  change (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).conj
        (Formalism.L2.Col.heckeFamI (formPts _ _) ∅ (offSubI.lev q.1, q.2)) f)).1 _ = _
  erw [conj_symm_apply]
  erw [Formalism.L2.Col.heckeI_op_apply]
  unfold Formalism.L2.Col.DecoPts.nbI
  simp [formPts]
  rfl

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).heckeLI i t)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
      (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
      fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF P hR
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ)
      (hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2) =>
    GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF q hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => GlobalTheory.T.levelChar_eq_one_inert_prime_off_level X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr L cV i t A k P hR q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.LiftBrg.InertTie
