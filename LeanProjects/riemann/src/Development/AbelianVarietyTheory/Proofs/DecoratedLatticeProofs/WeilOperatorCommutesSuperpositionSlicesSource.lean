import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSuperpos

variable {D : D7}

theorem pair_swap {S A B T : HSp D} (o : OrthDec S A B) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : Ω → WO B T) (a : Ω → ℂ) (hk : Measurable k) (ha : Integrable a μ)
    (ν : Measure (WO A T)) [IsFiniteMeasure ν]
    (Φ : WO S T → ℂ) (hΦc : Continuous Φ) (CΦ : ℝ) (hΦ : ∀ x, ‖Φ x‖ ≤ CΦ)
    (g : WO A T → ℂ) (hgc : Continuous g) (Cg : ℝ) (hg : ∀ x, ‖g x‖ ≤ Cg) :
    ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν =
      ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : SFinite ν := @instSFiniteOfSigmaFinite _ _ ν (@IsFiniteMeasure.toSigmaFinite _ _ ν _)
  obtain ⟨-, -, hA2, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, hB2, -⟩ := lattice_Mx D T.rank B.rank
  have hσ : Measurable fun q : WO A T × Ω => Φ ((o.resS T).symm (q.1, k q.2)) :=
    hΦc.measurable.comp ((o.continuous_resS_symm T).measurable.comp
      (measurable_fst.prodMk (hk.comp measurable_snd)))
  have hgm : Measurable fun q : WO A T × Ω => star (g q.1) :=
    (continuous_star.comp hgc).measurable.comp measurable_fst
  have h1 : Integrable (fun q : WO A T × Ω => a q.2) (ν.prod μ) := ha.comp_snd ν
  have hint : Integrable (Function.uncurry fun u w => a w * Φ ((o.resS T).symm (u, k w)) * star (g u))
      (ν.prod μ) := by
    refine (h1.norm.mul_const (CΦ * Cg)).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (h1.aestronglyMeasurable.mul hσ.aestronglyMeasurable).mul hgm.aestronglyMeasurable
    · rcases q with ⟨u, w⟩
      simp only [Function.uncurry_apply_pair, norm_mul, norm_star]
      have hC : 0 ≤ CΦ := (norm_nonneg _).trans (hΦ 0)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hΦ _) (hg _) (norm_nonneg _) hC) (norm_nonneg _)
  calc ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν
      = ∫ u, ∫ w, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂μ ∂ν := by
        congr 1; funext u; rw [integral_mul_const]
    _ = ∫ w, ∫ u, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
        congr 1; funext w; rw [← integral_const_mul]; congr 1; funext u; ring

theorem exists_sfinite {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ) (ha : Integrable a μ) :
    ∃ s : Set Ω, SigmaFinite (μ.restrict s) ∧ ∀ X : Ω → ℂ, ∫ w, a w * X w ∂μ = ∫ w, a w * X w ∂(μ.restrict s) := by
  have hf := ha.aefinStronglyMeasurable
  refine ⟨hf.sigmaFiniteSet, hf.sigmaFinite_restrict, fun X => ?_⟩
  have hs : MeasurableSet hf.sigmaFiniteSet := hf.measurableSet
  have h0 : ∀ᵐ w ∂μ, w ∉ hf.sigmaFiniteSet → a w = 0 := by
    have := hf.ae_eq_zero_compl
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at this
    exact this.mono fun w hw hws => hw hws
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero (h0.mono fun w hw hws => by rw [hw hws, zero_mul])).symm

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem comm_sfinite {S A B T : HSp D} (o : OrthDec S A B) {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hW : IsWeilDatumO ψ A T χ χ' om) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (k : Ω → WO B T) (a : Ω → ℂ)
    (hk : Measurable k) (ha : Integrable a μ) (p : GA D A × GA D T) (u₀ : WO A T) :
    om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ =
      ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  have hψ := hW.std
  set H : WO S T → ℂ := fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 with hH
  have hHt : IsThetaFunO ψ S T H := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p
  have hHs : ∀ u b, H ((o.resS T).symm (u, b)) = om p (fun u' => F ((o.resS T).symm (u', b))) u := by
    intro u b; simp only [hH, AddEquiv.apply_symm_apply]
  have hsl : ∀ b, IsThetaFunO ψ A T (fun u => F ((o.resS T).symm (u, b))) := by
    intro b
    have := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Unit (Measure.dirac ()) (fun _ => b) (fun _ => 1)
      measurable_const (integrable_const _)
    simpa using this
  set G : WO A T → ℂ := fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ with hGdef
  set R : WO A T → ℂ := fun u => ∫ w, a w * om p (fun u' => F ((o.resS T).symm (u', k w))) u ∂μ with hRdef
  have hG : IsThetaFunO ψ A T G := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Ω μ k a hk ha
  have hR' : R = fun u => ∫ w, a w * H ((o.resS T).symm (u, k w)) ∂μ := by
    funext u; simp only [hRdef, hHs]
  have hR : IsThetaFunO ψ A T R := by
    rw [hR']; exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o H hHt Ω μ k a hk ha
  have hL : IsThetaFunO ψ A T (om p G) := hW.om_pres p G hG
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank A.rank
  obtain ⟨hhaar, hfd, hvol⟩ := v.covol
  haveI := hhaar
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have key : ∀ g, IsThetaFunO ψ A T g → thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 R g := by
    intro g hg
    have hg' : IsThetaFunO ψ A T (om p⁻¹ g) := hW.om_pres _ _ hg
    have hinv : om p (om p⁻¹ g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨Cg, hCg⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg
    obtain ⟨Cg', hCg'⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg'
    obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hF
    obtain ⟨CH, hCH⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hHt
    calc thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 (om p G) (om p (om p⁻¹ g)) := by rw [hinv]
      _ = thPair v.μ v.𝓕 G (om p⁻¹ g) := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ hG hg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => F ((o.resS T).symm (u, k w))) (om p⁻¹ g) ∂μ := by
          unfold thPair
          exact pair_swap o μ k a hk ha _ F hF.cont CF hCF _ hg'.cont Cg' hCg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (om p (fun u => F ((o.resS T).symm (u, k w)))) g ∂μ := by
          congr 1; funext w; congr 1
          rw [← GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ (hsl _) hg', hinv]
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => H ((o.resS T).symm (u, k w))) g ∂μ := by
          simp only [hHs]
      _ = thPair v.μ v.𝓕 R g := by
          rw [hR']; unfold thPair
          exact (pair_swap o μ k a hk ha _ H hHt.cont CH hCH g hg.cont Cg hCg).symm
  have hd : IsThetaFunO ψ A T (om p G - R) := GlobalTheory.WeilVacMove.isTheta_sub hL hR
  have hkd := key _ hd
  obtain ⟨CL, hCL⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hL
  obtain ⟨CR, hCR⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hR
  obtain ⟨Cd, hCd⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hd
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  have bint : ∀ f : WO A T → ℂ, Continuous f → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) →
      Integrable (fun x => f x * star ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    intro f hf C hC
    refine (integrable_const (C * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hf.mul (continuous_star.comp hd.cont)).aestronglyMeasurable
    · rw [norm_mul, norm_star]
      exact mul_le_mul (hC x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  have h0 : ∫ x in v.𝓕, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) ∂v.μ = 0 := by
    have e : ∀ x, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) =
        om p G x * star ((om p G - R) x) - R x * star ((om p G - R) x) := by
      intro x
      rw [← sub_mul, ← Pi.sub_apply, Complex.star_def, Complex.mul_conj]
    simp only [e]
    rw [integral_sub (bint _ hL.cont CL hCL) (bint _ hR.cont CR hCR)]
    unfold thPair at hkd
    rw [hkd, sub_self]
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ x in v.𝓕, Complex.normSq ((om p G - R) x) ∂v.μ = 0 := by exact_mod_cast h0
  have hnn : 0 ≤ᵐ[v.μ.restrict v.𝓕] fun x => Complex.normSq ((om p G - R) x) :=
    Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _
  have hi : Integrable (fun x => Complex.normSq ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    refine (integrable_const (Cd * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_normSq.comp hd.cont).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hCd x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hCd x))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h1
  have hae' : ∀ᵐ x ∂v.μ.restrict v.𝓕, (om p G - R) x = 0 :=
    hae.mono fun x hx => Complex.normSq_eq_zero.1 hx
  obtain ⟨i1, -, i3, -, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i3; haveI := i5
  have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratMx D T.rank A.rank) v.μ v.𝓕 hfd (om p G - R) hd.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hd) hae'
  have := congrFun hz u₀
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem weil_comm_superpos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  intro D ψ S A B T o χ χ' om hW F hF Ω _ μ k a hk ha p
  refine ⟨(GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p, fun u₀ => ?_⟩
  obtain ⟨s, hs, hr⟩ := exists_sfinite μ a ha
  have e1 : (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) =
      fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂(μ.restrict s) := funext fun u => hr _
  rw [e1, hr]
  exact comm_sfinite o hW hF (μ.restrict s) k a hk ha.restrict p u₀

end GlobalTheory.WeilSuperpos
