import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFoldViaLintegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnScalarFormNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFunctionContinuousOnBesselGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem mul_mem_sfin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u)
    {g : X.B.I.Gf} (hg : g ∈ Hfin X u) : n * g ∈ SfinU X u := by
  have hfix : ∀ y ∈ fixSet X u, X.B.I.fmat g *ᵥ incl X.B.I y = incl X.B.I y := hg
  have hm : X.B.I.fmat (n * g) = X.B.I.fmat n * X.B.I.fmat g := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y ∈ fixSet X u,
      (X.B.I.fmat (n * g) - 1) *ᵥ incl X.B.I y = (X.B.I.fmat n - 1) *ᵥ incl X.B.I y := by
    intro y hy
    rw [hm, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix y hy]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key _ (Or.inl (Or.inl ⟨a, rfl⟩))]; exact hn.1 a
  · rw [key _ (Or.inr rfl)]; exact hn.2.1

theorem ph_supp (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (x : X.B.I.GA)
    (hx : Ph X u hK T x ≠ 0) : ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
  unfold Ph at hx
  split_ifs at hx with hd
  · obtain ⟨n, g, k, hdec⟩ := hd
    obtain ⟨hn, hk, he⟩ := hdec
    exact ⟨n * (g : X.B.I.Gf), mul_mem_sfin X u hn g.2, k, hk, he⟩
  · exact absurd rfl hx

end GlobalTheory.Core.MiFold

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  simp only [psiBes, psiE]; exact hψ.2.1 _

theorem iota_mul_assoc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ s : GA D (D.sp.Y 0)) (y : X.B.I.Ginf) (x : X.B.I.Gf) :
    iotaX X h (γ * s) * (y, x) = iotaX X h γ * (iotaX X h s * (y, x)) := by
  rw [map_mul]
  exact mul_assoc _ _ _

end GlobalTheory.Core.MiFold

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.MiFold in

theorem GlobalTheory.Core.Mi.unfoldedPer : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter), IsStdChar D ψ (-1) → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℂ, ∀ (T : Cu X u hK), IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) ∧ ∀ f : X.B.I.GA → ℂ, RowFun X f → ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u) := by
  intro D X h u ψ A B hK hψ Fs hFs
  obtain ⟨-, -, -, 𝓢, h𝓢, h𝓢fin, hI⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev
  obtain ⟨c, hc, hQ⟩ := GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions D X h u ψ A B 𝓢 h𝓢 Fs hFs
  refine ⟨(c : ℂ), fun T => ?_⟩
  have hPh := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u) T
  have hgrp := GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B
  have hph := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T

  set Φ : X.B.I.Ginf → besGrp B.d B.o → X.B.I.GA := fun y s => iotaX X h s.1 * (y, X.xu u) with hΦdef
  have hι : Continuous fun s : besGrp B.d B.o => iotaX X h s.1 := (iotaX X h).continuous.comp continuous_subtype_val
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).1 * p.1 :=
      ((continuous_fst.comp hι).measurable.comp measurable_snd).mul measurable_fst
    have h2 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).2 * X.xu u :=
      ((continuous_snd.comp hι).measurable.comp measurable_snd).mul_const _
    exact h1.prodMk h2

  obtain ⟨C, hC⟩ := GlobalTheory.T.bessel_column_scalar_form_norm_bound D X h u ψ A B hK T
  have hbd : ∀ y (s : besGrp B.d B.o), ‖Ph X u hK T (Φ y s)‖ ≤ C * ‖X.Wu u y‖ := by
    intro y s
    obtain ⟨n, hn, a, ha⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s.1).1 s.2
    simp only [hΦdef, ha, hph.2 n hn a y, norm_mul, norm_star, norm_psiBes hψ.1, one_mul]
    exact hC _ _
  have hWu : ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) < ⊤ := (X.Wu_spec u).2.2.2.1
  have hfin : ∀ K : ℝ, 0 ≤ K → ∀ G : X.B.I.GA → ℂ, (∀ x, ‖G x‖ ≤ K * ‖Ph X u hK T x‖) →
      ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u) < ⊤ := by
    intro K hK0 G hG
    have hpt : ∀ y (s : besGrp B.d B.o), ‖G (Φ y s)‖ₑ ≤ ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ := by
      intro y s
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((hG _).trans ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hbd y s).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))) hK0
    calc ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u)
        ≤ ∫⁻ y, B.lev.μR 𝓢 * (ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ) ∂(X.nuQ u) := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ≤ ∫⁻ s in 𝓢, ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ ∂B.lev.μR :=
                lintegral_mono fun s => hpt y s
            _ = _ := by rw [setLIntegral_const, mul_comm]
      _ = B.lev.μR 𝓢 * ENNReal.ofReal (K * |C|) * ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) := by
          rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top h𝓢fin.ne ENNReal.ofReal_ne_top)]
          simp only [mul_assoc]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top h𝓢fin ENNReal.ofReal_lt_top) hWu

  set P : (X.B.I.GA → ENNReal) → Prop := fun F => (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) ∧
    (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) ∧
    (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) with hPdef
  have hQ' : ∀ F : X.B.I.GA → ENNReal, Measurable F → P F →
      ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (Φ y s) ∂B.lev.μR ∂(X.nuQ u) :=
    fun F hF hP => hQ F hF hP.1 hP.2.1 hP.2.2
  have hsupp : ∀ G : X.B.I.GA → ℂ, (∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0) → ∀ φ : ℂ → ENNReal, φ 0 = 0 →
      ∀ x, φ (G x) ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
    intro G hG φ hφ x hx
    refine ph_supp X u hK T x (hG x ?_)
    intro h0; rw [h0, hφ] at hx; exact hx rfl
  have hchi : ∀ k ∈ X.K2, ‖X.chi2 k‖ = 1 := hK.2.2.2.2

  have hint : IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) := by
    refine ⟨hPh.1.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hQ' (fun x => ‖Ph X u hK T x‖ₑ) hPh.1.enorm ⟨fun γ hγ x => by dsimp only; rw [hPh.2.1 γ hγ x],
      fun k hk x => by dsimp only; rw [hPh.2.2.1 x k hk, enorm_mul, ← ofReal_norm_eq_enorm (X.chi2 k), hchi k hk,
        ENNReal.ofReal_one, one_mul],
      hsupp (Ph X u hK T) (fun x hx => hx) (fun z => ‖z‖ₑ) enorm_zero⟩]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin 1 zero_le_one _ fun x => by rw [one_mul])
  refine ⟨hint, fun f hf => ?_⟩
  obtain ⟨Cf, hCf⟩ := hf.bdd
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 1)
  have hfm : Measurable f := hf.cont.measurable

  obtain ⟨G, hGdef⟩ : ∃ G : X.B.I.GA → ℂ, G = fun x => f x * Ph X u hK T x := ⟨_, rfl⟩
  have hGl : ∀ γ ∈ Srat X u, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    simp only [hGdef, hPh.2.1 γ hγ x, hf.left γ (Subgroup.mem_inf.1 hγ).1 x]
  have hGr : ∀ k ∈ X.K2, ∀ x, G (x * (1, k)) = G x := by
    intro k hk x
    have h1 : star (X.chi2 k) * X.chi2 k = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hchi k hk]; norm_num
    simp only [hGdef, hPh.2.2.1 x k hk, hf.right k hk x]
    calc star (X.chi2 k) * f x * (X.chi2 k * Ph X u hK T x) = (star (X.chi2 k) * X.chi2 k) * (f x * Ph X u hK T x) := by ring
      _ = _ := by rw [h1, one_mul]
  have hGs : ∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0 := fun x hx h0 => hx (by simp only [hGdef, h0, mul_zero])
  have hGm : Measurable G := by rw [hGdef]; exact hfm.mul hPh.1
  have hGb : ∀ x, ‖G x‖ ≤ Cf * ‖Ph X u hK T x‖ := fun x => by
    rw [hGdef, norm_mul]; exact mul_le_mul_of_nonneg_right (hCf x) (norm_nonneg _)
  obtain ⟨-, hfold⟩ := GlobalTheory.T.integral_fold_via_lintegral_formula (X.B.I.muA X.B.μf) Fs (X.nuQ u) B.lev.μR 𝓢 h𝓢fin Φ hΦ c hc.le P hQ' G hGm
    (fun φ hφ => ⟨fun γ hγ x => by simp only [hGl γ hγ x], fun k hk x => by simp only [hGr k hk x],
      hsupp G hGs φ hφ⟩) (hfin Cf hCf0 G hGb)
  rw [show (∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf)) = ∫ x in Fs, G x ∂(X.B.I.muA X.B.μf) by rw [hGdef], hfold]
  subst hGdef
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)

  have hcont : ContinuousOn (fun g => f (iotaX X h g * (y, X.xu u)) * Ph X u hK T (iotaX X h g * (y, X.xu u)))
      (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
    refine ContinuousOn.mul ?_ (GlobalTheory.T.bessel_column_function_continuousOn_bessel_group D X h u ψ A B hK T y hψ.1)
    exact (hf.cont.comp ((iotaX X h).continuous.mul continuous_const)).continuousOn
  have hinv : ∀ γ ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o,
      f (iotaX X h (γ * s) * (y, X.xu u)) * Ph X u hK T (iotaX X h (γ * s) * (y, X.xu u)) =
        f (iotaX X h s * (y, X.xu u)) * Ph X u hK T (iotaX X h s * (y, X.xu u)) := by
    intro γ hγ s _
    have hγ' := (hgrp.2 γ).1 hγ
    have := hGl _ hγ' (iotaX X h s * (y, X.xu u))
    dsimp only at this
    exact (congrArg (fun z => f z * Ph X u hK T z) (iota_mul_assoc X h γ s y (X.xu u))).trans this
  have hIy := (hI _ hcont hinv).2
  refine hIy.trans ?_
  simp only [BesLev.per, besPer, besFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hph.2 n.1 n.2 a y]
  ring
