import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlpBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.DataInst

variable {D : D7} (X : HidaSetting D)

theorem alX_eq (hEta : EtaTie X) (u u' : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    alX X u u' v = alpD u u' (plEquiv X v) := by
  have haP : ∀ T : ℕ, aP (E := X.B.I.E) v D.R.k X.B.I.n T = aPD (plEquiv X v) T := by
    intro T
    unfold aP aPD
    have hI : Finset.Icc (if ((T : 𝓞 X.B.I.F) ∈ v.asIdeal) then D.R.k else D.R.k + 1) X.B.I.n =
        Finset.Icc (if ((T : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal) then D.R.k else D.R.k + 1) D.R.r := by
      rw [X.n_eq]
      by_cases hm : ((T : 𝓞 X.B.I.F) ∈ v.asIdeal)
      · rw [if_pos hm, if_pos ((natCast_mem_plEquiv X v T).2 hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((natCast_mem_plEquiv X v T).1 h))]
    rw [hI]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hEta v, absNorm_plEquiv]
  unfold alX alpD Tw
  rw [haP, haP]
  by_cases h : TypAt X v
  · rw [if_pos h, if_pos ((typAt_iff X v).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((typAt_iff X v).2 h'))]

theorem summable_log_alpD (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    (∀ p, 0 < alpD u u' p) ∧ Summable fun p => Real.log (alpD u u' p) := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  have hα := Formalism.L2.SG.IntegralApproximation.AlpBound_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := hα hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  refine ⟨hal0, ?_⟩
  refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
  have h2 := Real.log_le_log (hal0 p) (hαb p).2
  rw [Real.log_exp] at h1 h2
  have ha' : a p = (Formalism.L2.SG.DataCut.qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
  constructor <;> linarith

theorem prod_split {β : Type} (f : β → ℝ) (s : Finset β) (hpos : ∀ v, 0 < f v)
    (hlog : Summable fun v => Real.log (f v)) :
    (∏ p : ↥s, f p.1) * ∏' v : {v // v ∉ s}, f v.1 = ∏' v, f v := by
  have hls : Summable (fun v : {v // v ∉ s} => Real.log (f v.1)) :=
    hlog.comp_injective (i := fun v : {v // v ∉ s} => v.1) Subtype.val_injective
  have hO : ∏' v : {v // v ∉ s}, f v.1 = Real.exp (∑' v : {v // v ∉ s}, Real.log (f v.1)) :=
    (Real.rexp_tsum_eq_tprod (f := fun v : {v // v ∉ s} => f v.1) (fun v => hpos v.1) hls).symm
  have hT : ∏ p : ↥s, f p.1 = Real.exp (∑ p : ↥s, Real.log (f p.1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => (Real.exp_log (hpos _)).symm
  have hsplit : ∑ p : ↥s, Real.log (f p.1) + ∑' v : {v // v ∉ s}, Real.log (f v.1) = ∑' v, Real.log (f v) := by
    rw [Finset.sum_coe_sort s (fun x => Real.log (f x))]
    exact hlog.sum_add_tsum_compl (s := s)
  rw [hO, hT, ← Real.exp_add, hsplit, Real.rexp_tsum_eq_tprod hpos hlog]

theorem locOf_al_eq (hEta : EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    (locOf X u u' ψ).al = ∏' q, alpD u u' q := by
  obtain ⟨hpos, hlog⟩ := summable_log_alpD hk u u'
  have he : ∀ v, alX X u u' v = alpD u u' (plEquiv X v) := alX_eq X hEta u u'
  have hxpos : ∀ v, 0 < alX X u u' v := fun v => (he v).symm ▸ hpos _
  have hxlog : Summable fun v => Real.log (alX X u u' v) := by
    have h1 : Summable fun v => Real.log (alpD u u' (plEquiv X v)) := (plEquiv X).summable_iff.2 hlog
    exact h1.congr fun v => by rw [he v]
  have hS := prod_split (alX X u u') (Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hxpos hxlog
  have hR : ∏' v, alX X u u' v = ∏' q, alpD u u' q := by
    rw [tprod_congr he]
    exact (plEquiv X).tprod_eq (alpD u u')
  rw [← hR, ← hS]
  rfl

end Formalism.L2.SG.Pf.AlTie

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem AlTieC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hEta : AlTie.EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq := by
  unfold AlTieC
  exact AlTie.locOf_al_eq X hEta hk u u' ψ

theorem AlTieC_of_loc {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq :=
  AlTieC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (AlTie.etaTie_of X hL) hk

end Formalism.L2.SG.Pf
