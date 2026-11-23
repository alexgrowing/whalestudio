import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionOntoFiniteGroupSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdDecoratedLatticeRightTranslateLevelQStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagLiftTranslationMemTypeLevelCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem formRho_one_apply {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
    (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet Xf.E n ST SG)) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)
    (h : Λ.grp) (v : C.V) :
    Formalism.L2.Col.formRho C Λ ((1 : Formalism.L2.Col.UF Xf.E n), h) v = ((Λ.chr h : Xf.Kˣ) : Xf.K) • v := by
  show (((Λ.chr h : Xf.Kˣ) : Xf.K) • C.rho 1) v = _
  rw [map_one]
  rfl

set_option maxHeartbeats 8000000 in
theorem act_key (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (P : PresL X I hX U Xg tr L cV i t)
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q)
    (h : Formalism.L2.Col.GLG X.B.fields.E X.B.R.nV (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
    (hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
    (hpt : ∀ x : Bridge.Gf (Vc X.toD7 i), ptS X I U i t A k (x * κ) =
      ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
        h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
        ptS X I U i t A k x)
    (hch : X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ))
    (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (x : Bridge.Gf (Vc X.toD7 i)) :
    P.coef (((Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ) φ :
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) :
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (ptL X I U i t A k x)) =
      (((envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptL X I U i t A k (x * κ))) := by
  have h1 := φ.2 (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ⟨h, hh⟩) :
      Formalism.L2.Col.FormG (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv)
      (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)
  have h2 : (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ)) =
      ((((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K)) •
        (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x) := by
    rw [hpt x, ← one_mul (1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ← Prod.mk_mul_mk, mul_smul]
    exact h1.trans (formRho_one_apply _ _ _ _)
  refine Eq.trans (congrArg P.coef (Formalism.L2.Col.trRep_apply _ _ _ _ _ φ _)) ?_
  have h3 : P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ))) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)) := by
    rw [h2]
    refine (P.coef.map_smulₛₗ _ _).trans ?_
    rw [hch]
  exact (inv_smul_smul ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ) _).symm.trans (congrArg _ h3.symm)

theorem lemT : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ h : Formalism.L2.Col.GLG X.B.fields.E X.B.R.nV (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
        ∃ hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
          (∀ x : Bridge.Gf (Vc X.toD7 i), LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
            ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
              h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ))⁻¹) •
              LiftBrg.ActQ.ptS X I U i t A k x) ∧
          X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
            (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG i t A k hA κ
  obtain ⟨hh, hc⟩ := GlobalTheory.T.flagLift_translation_mem_typeLevel_character X px I U L eG hI hV hL hG i t A k hA κ
  refine ⟨_, hh, fun x => ?_, hc⟩
  rw [GlobalTheory.T.stdDecoratedLattice_rightTranslate_levelQ X px I U L hI hV hL i t A k hA κ x, mul_inv_cancel_right]

set_option maxHeartbeats 4000000 in
theorem lemAct : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∀ (g : Gc X.B px) (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q), LiftBrg.ActQ.redQ X I U L eG i t κ = g →
      ∀ f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms,
        P.ext ((((famR X I hX U Xg tr).A.leftGroupActionLift i t g f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms)) : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) =
          Bridge.g0Act (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP g κ hκ f
  obtain ⟨h, hh, hpt, hch⟩ := lemT X px I U L eG hI hV hL hG i t A k hA κ
  subst hκ
  funext x
  have e1 := hP ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f) x
  have e2 := hP f (x * κ)
  unfold Bridge.g0Act
  refine e1.trans ?_
  refine Eq.trans ?_ (congrArg (fun w => (((LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) • w) e2).symm
  have e3 : (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
      ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f)) =
      Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ)
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f) :=
    LinearEquiv.symm_apply_apply _ _
  rw [e3]
  exact act_key X I hX U Xg tr L eG cV i t A k P κ h hh hpt hch _ x

theorem exists_actTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∃ a : Bridge.ActTie (Bridge.ratF (Vc X.toD7 i)) P (LiftBrg.envL X I hX U Xg tr L cV i t).lev.Q
        (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch ((famR X I hX U Xg tr).A.leftGroupActionLift i t),
      ∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG (a.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP
  refine ⟨{ red := redQ X I U L eG i t
            red_surj := GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective X px I U L eG hI hV hL hG i t
            red_ker := fun q => redQ_eq_one_iff X I U L eG i t q
            act_eq := lemAct X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP }, fun q => ?_⟩
  exact eG_redQ X I U L eG i t q

end GlobalTheory.Mem.R3.LiftBrg.ActQ
