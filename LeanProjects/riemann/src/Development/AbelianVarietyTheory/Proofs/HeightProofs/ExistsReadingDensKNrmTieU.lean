import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Formalism.LocalToGlobal.ProjectiveLattices.SupPTGePf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictCompInt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PnContinuous

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.HeightDefinite.Generic

theorem supPTGe_of_fnPin : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))), (∀ Z, CBase hG Z (yP Z)) → ∀ ka : WeightFamilies.Wt D j, SupPTGe h j hG fn yP ka := by
  intro D T h j hj fn hfn hG yP hyP ka Z F hF hev
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ => h.unf j hj σ hσ
  have hFc : F.1 ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) T.Q.c (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
      (wtA ka) ka.n := cutR_le T.C j ka F.2
  obtain ⟨g, hg, h1, h0, hI⟩ := GlobalTheory.Reg.exists_cusp_restrict_comp_int _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU hG Z (wtA ka) ka.n F.1 hFc
  have hg' : g ∈ cutR T.C j ka := by
    rw [cutR_eq T.C hj]; exact hg
  have hx : 0 < xiR D := (GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.1
  refine ⟨⟨g, hg'⟩, ?_, ?_, fun sg => ?_⟩
  · intro la v hv
    have hFv := hF la v hv
    obtain ⟨⟨q, Tc, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
    change 0 ≤ nval Tc.V e (evI y g)
    change 0 ≤ nval Tc.V e (evI y F.1) at hFv
    rcases hI Tc io y with h2 | h2
    · rw [h2]; exact hFv
    · rw [h2, nval_zero]; exact le_top
  · intro h2
    have h3 : g = 0 := congrArg Subtype.val h2
    apply hev
    change evC hG Z F.1 = 0
    rw [← h1, h3, evC_zero]
  · have h4 := (GlobalTheory.HeightDefinite.Generic.supC_le_iSup_generic _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU (xiR D) fn hx hfn hG yP hyP (wtA ka) ka.n (dom_wtA ka) Z
      F.1 hFc g hg h1 h0 sg).2
    change cutN T.C T.Ns j ka sg ⟨g, hg'⟩ ≤ _
    unfold cutN
    rw [if_pos hj]
    exact h4

theorem exists_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR)
    (hfn : GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) xR fn)
    (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) :
    ∃ (k : (U (goodOf c σ)).Comp) (x : ((U (goodOf c σ)).X k).dom), ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n,
      Formalism.L2.Pj.ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y =
        recNrm (U (goodOf c σ)) xR a n f k x.1 := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm E H Dw l Xo c r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hU xR fn hx hfn
  have hg := goodEmb_goodOf c σ
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    rw [e]
    obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
    exact ⟨k, x, fun a n hd f hf => h2 σ hσ k x t y ht a n hd f hf⟩
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    rw [e] at hg ⊢
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _
      (GlobalTheory.FrameNorm.conjAlg σ) y
    obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 y'
    exact ⟨k, x, fun a n hd f hf => (h3 σ y y' hy' a n f hf).symm.trans (h2 _ hg k x t y' ht a n hd f hf)⟩

theorem exists_reading_densK_nrmTieU : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))), (∀ Z, CBase hG Z (yP Z)) → ∃ pt : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ), SupPtAt (Tc := T) j (goodOf T.Q.c (sgOf P)), (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) a n, Dom a n → ∀ F ∈ sec (T.Q.Xo j) T.Q.c a n, nrmC fn (yP Z) (wtZ a n) (valC hG a n F Z) P = recNrm (T.U j (goodOf T.Q.c (sgOf P))) (xiR D) a n F (pt Z P).1 (pt Z P).2.1) ∧ (∀ ka : WeightFamilies.Wt D j, DensK h j hG ka pt) ∧ ∀ (N : ℕ) (wR : Fin (N + 1) → T.R j) (uL : WtR D.host.E) (etR : T.R j) (uet : WtR D.host.E), Dom uL.1 uL.2 → Dom uet.1 uet.2 → (∀ k, wR k ∈ sec (T.Q.Xo j) T.Q.c uL.1 uL.2) → etR ∈ sec (T.Q.Xo j) T.Q.c uet.1 uet.2 → NrmTieU hG fn yP (T.U j) (xiR D) wR uL etR uet := by
  intro D T h j hj fn hfn hG yP hyP
  have hx : 0 < xiR D := (GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.1
  have hU := h.unf j hj
  have h3 := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ (T.Q.Xo j) T.Q.c _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU (xiR D) fn hx hfn hG yP hyP).2.2
  choose k x hkx using fun (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) =>
    exists_frame (T.U j) hU (xiR D) fn hx hfn (sgOf P) (yP Z P)
  have key : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) a n, Dom a n → ∀ F ∈ sec (T.Q.Xo j) T.Q.c a n,
      nrmC fn (yP Z) (wtZ a n) (valC hG a n F Z) P =
        recNrm (T.U j (goodOf T.Q.c (sgOf P))) (xiR D) a n F (k Z P) (x Z P).1 :=
    fun Z P a n hd F hF => (h3 Z P a n F hF).trans (hkx Z P a n hd F hF)
  refine ⟨fun Z P => ⟨k Z P, ⟨(x Z P).1, (x Z P).2⟩⟩, key, fun ka Z F hF hev => ?_,
    fun N wR uL etR uet hL he hw het Z P => ?_⟩
  · obtain ⟨F', hF', hne, hsup⟩ := supPTGe_of_fnPin D T h j hj fn hfn hG yP hyP ka Z F hF hev
    refine ⟨F', hF', hne, fun sg => (hsup sg).trans (le_of_eq ?_)⟩
    exact iSup_congr fun P => key Z P _ _ (dom_wtA ka) _ (cusp_le_sec _ _ _ _ _ (cutR_le T.C j ka F.2))
  · exact ⟨goodOf T.Q.c (sgOf P), goodEmb_goodOf _ _, k Z P, (x Z P).1, (x Z P).2,
      fun i => key Z P _ _ hL _ (hw i), (key Z P _ _ he _ het).le⟩

end GlobalTheory.HeightDefinite.Generic
