import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselModelDoublingDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHoldsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.BotPin

variable {D : D7}

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

theorem per_congr {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B₁ B₂ : BesLev D ρ} (h : B₁ = B₂) (φ₁ : GA D B₁.A → ℂ)
    (φ₂ : GA D B₂.A → ℂ) (hφ : HEq φ₁ φ₂) (f₁ : GA D B₁.V → ℂ) (f₂ : GA D B₂.V → ℂ) (hf : HEq f₁ f₂) :
    B₁.per ψ φ₁ f₁ = B₂.per ψ φ₂ f₂ := by
  subst h; cases hφ; cases hf; rfl

end GlobalTheory.Core.Mi.BotPin

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Mi.BotPin in

theorem GlobalTheory.Core.Mi.bot_of_pinBot : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u), GlobalTheory.Core.Mi.IdE S.X → GlobalTheory.Count.GapGe S.X.B (100 * (D.R.r : ℝ) ^ 4) → PinBot S d → d.Base → d.Bot := by
  intro hDS hCR D u F₀ S d hIdE hGap hPin hBase
  obtain ⟨h0, B, a₀, a, hBlev, hAd, hH0, haf, hac, hMatch, hrd⟩ := hPin
  obtain ⟨R, hRinj, hR⟩ := GlobalTheory.T.bessel_column_form_central_translation D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y.hK a hIdE haf hac
  obtain ⟨ξ, hξspan, hξ⟩ := GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm D S.X S.inst u d.c.ψ B (F₀ u) (S.tr u) S.Y.hK d.c.θ a₀ hBase.com.inf hIdE
    hAd hH0 (S.lev u)
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)
  let T0 : (D.mem u).A.Mram →ₗ[ℂ] Cu S.X u S.Y.hK := e.symm.toLinearMap ∘ₗ Submodule.inclusion hram
  let V : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u :=
    ((S.hI S.hF).eCu u).symm.toLinearEquiv.toLinearMap ∘ₗ R ∘ₗ T0
  refine ⟨V, ?_, ?_⟩
  · exact ((S.hI S.hF).eCu u).symm.injective.comp
      (hRinj.comp (e.symm.injective.comp (Submodule.inclusion_injective hram)))

  · intro φ hvan
    let T : Cu S.X u S.Y.hK := T0 φ
    have hφT : Formalism.L2.SG.ColDict.colDictL S.X (S.tr u) S.Y.hK T = φ.1 := by
      have := congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram φ))
      exact this
    have hm : 0 < D.R.m := by omega
    have hst := hBase.st 0 hm
    have hcontT : ∀ ξ', IsContAut (D.sp.X 0) (B.colForm T.1 ξ') :=
      (GlobalTheory.T.fourier_coefficient_bessel D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y.hK T).1
    have hcontR : ∀ ξ', IsContAut (D.sp.X 0) (B.colForm (R T).1 ξ') :=
      (GlobalTheory.T.fourier_coefficient_bessel D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y.hK (R T)).1
    let t : GA D (D.sp.Y 0) := ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from d.t 0)
    have hvan' : ∀ G ∈ MultT d.c.θ (d.st 0).M (d.lev 0) (levChi (D.sp.Y 0) d.bot.β d.bot.L), ∀ ξ' x,
        B.lev.per d.c.ψ (B.colForm (R T).1 ξ') (rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x)) = 0 := by
      intro G hG ξ' x
      have hf : IsContAut (D.sp.Y 0) (rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x)) :=
        isContAut_rTrans _ (isContAut_multT hG x)
      have hy : ∀ y, B.lev.per d.c.ψ (B.colForm (R T).1 (ξ y))
          (rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x)) = 0 := by
        intro y
        have h1 := hvan D.R.rS h0 ⟨G, hG⟩ y x
        have h3 := GlobalTheory.T.bessel_period_right_translation_invariant D d.c.ψ D.R.rS B.lev (rTrans a₀⁻¹ (B.colForm T.1 (ξ y))) (rTrans (d.t 0) (G x)) (a₀ * a)
          hBase.com.std (isContAut_rTrans _ (hcontT (ξ y))) (isContAut_rTrans _ (isContAut_multT hG x))
        have e1 : B.colForm (R T).1 (ξ y) = rTrans (a₀ * a) (rTrans a₀⁻¹ (B.colForm T.1 (ξ y))) := by
          rw [hR T (ξ y)]
          funext g
          simp only [rTrans]
          congr 1
          rw [Subgroup.mem_center_iff.1 hac a₀]
          group
        have e2 : rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x) =
            rTrans (embA B.d B.o (a₀ * a)) (rTrans (d.t 0) (G x)) := by
          funext g
          show G x (g * ((iotaX S.X S.inst).symm (1, S.X.xu u) * t)) =
            G x (g * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0))
          refine congrArg (G x) ?_
          change g * ((iotaX S.X S.inst).symm (1, S.X.xu u) * (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
            embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0))) = _
          rw [mul_assoc ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ (embA B.d B.o (a₀ * a)), mul_inv_cancel_left]
          exact (mul_assoc _ _ _).symm
        have e4 : rTrans a₀⁻¹ (B.colForm T.1 (ξ y)) = d.rd 0 φ.1 y := by
          rw [hrd, ← hφT]
          funext g
          exact (hξ T y g).symm
        have e3 : B.lev.per d.c.ψ (rTrans a₀⁻¹ (B.colForm T.1 (ξ y))) (rTrans (d.t 0) (G x)) = 0 := by
          rw [e4]
          exact (per_congr hBlev _ _ HEq.rfl _ _ HEq.rfl).trans h1
        rw [e1, e2]
        exact h3.trans e3
      have hmem : ξ' ∈ Submodule.span ℂ (Set.range ξ) := by rw [hξspan]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
      have hlin : B.colForm (R T).1 ξ' = ∑ i ∈ c.support, c i • B.colForm (R T).1 (ξ i) := by
        rw [← hc]
        funext g
        simp only [SBes.colForm, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
      rw [hlin, GlobalTheory.T.period_sum_holds D d.c.ψ hBase.com.std D.R.rS B.lev _ hf _ c.support c (fun i => B.colForm (R T).1 (ξ i))
        (fun i _ => hcontR (ξ i))]
      exact Finset.sum_eq_zero fun i _ => by rw [hy i, mul_zero]
    have hP := GlobalTheory.T.puFun_eq_zero_of_per_colForm_eq_zero hDS hCR D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y d.c.θ (d.st 0).par (d.st 0).M (d.lev 0)
      (levChi (D.sp.Y 0) d.bot.β d.bot.L) t hst.par hBase.com.inf hBase.com.std hGap hIdE hMatch (S.hF.inHH u) (R T) hvan'
    have hPu := (S.hI S.hF).Pu_eq u (V φ)
    have e5 : (S.hI S.hF).eCu u (V φ) = R T := LinearIsometryEquiv.apply_symm_apply _ _
    rw [e5] at hPu
    have e6 : (Formalism.L2.SG.PackageTie2.sOf S.hF).Pu u (R T) = 0 := Subtype.ext hP
    rw [e6] at hPu
    exact (LinearIsometryEquiv.map_eq_zero_iff _).1 hPu
