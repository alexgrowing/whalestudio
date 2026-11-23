import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FubiniCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGraStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem enorm_fl_le {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (Th : GA D V → ℂ) (hTh : ∀ n, ‖Th n‖ ≤ 1)
    (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    ‖fl ψ d W v vb vU Th x Ψ‖ₑ ≤
      ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ v.μ v.𝓕 Ψ (x ⬝ u.1.1) (x ⬝ b)‖ₑ ∂vb.μ ∂vU.ν := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun u => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun b => ?_)
  simp only [flFun]
  rw [enorm_mul]
  refine mul_le_of_le_one_left' ?_
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_one.2 (hTh _)

theorem liftS_mul {D : D7} {V W : HSp D} (om : Om V W) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (G : GA D W → ℂ)
    (Φ : WO V W → ℂ) (n g : GA D V) : liftS om μ 𝓕 G Φ (n * g) = liftS om μ 𝓕 G (om (g, 1) Φ) n := by
  have e : ∀ h, thetaKO om (n * g) h Φ = thetaKO om n h (om (g, 1) Φ) := fun h => by
    simp only [thetaKO]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [liftS, Formalism.IndefR.Lift.liftInt, e]

theorem besPer_lift_eq_integral_kerBF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ 𝓑 : Set (GA D J.W), IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ → IntegrableOn (kerBF s φ G Φ) 𝓑 s.vW.μ ∧ B.per ψ φ (s.lift G Φ) = ∫ h in 𝓑, kerBF s φ G Φ h ∂s.vW.μ := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ 𝓑 h𝓑
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨hb, hg, hx, hR, -, -⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  have hemb : Continuous (embA B.d B.o) :=
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D B.V B.V₀ ρ B.d).2.2.2.2.1.comp
      (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hTh := GlobalTheory.T.conjBesselCharacter_isUnfoldingThetaFunction_of_gram_zero D ψ s.weil.std ρ B J.W J.d.e hg
  have h𝓑' := h𝓑
  rw [← hR] at h𝓑'
  set Th : GA D B.V → ℂ := fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) with hThd
  have hn : ∀ n, ‖Th n‖ ≤ 1 := fun n => by
    simp only [hThd, norm_star, psiBes, psiE]
    exact (s.weil.std.1.2.1 _).le
  have hfl : ∀ p, fl ψ B.d J.W s.vS s.vT s.vU Th (rat J.d.e) (s.om p Φ) = flatBF s (s.om p Φ) 0 := fun p => by
    rw [← hx]
    exact GlobalTheory.T.flagUnipotentUnfolding_besselFourierJacobi_eq D ψ ρ B J s _ (s.weil.om_pres p Φ hΦ)
  have hom : ∀ g h, s.om (1, h) (s.om (g, 1) Φ) = s.om (g, h) Φ := fun g h => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

  have h1 : ∀ g, ∫ n in B.vN.𝓝, Th n.1 * s.lift G Φ (n.1 * g) ∂B.vN.ν =
      ∫ h in 𝓑, G h * flatBF s (s.om (g, h) Φ) 0 ∂s.vW.μ := fun g => by
    have := (GlobalTheory.T.unfold_over_flagUnipotent_thetaLift D hD ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS B.vN s.vT s.vU s.vW J.d.e Th
      hb hTh G (s.om (g, 1) Φ) hG (s.weil.om_pres _ Φ hΦ) 𝓑 h𝓑').2
    simp only [hom, hfl] at this
    simp only [Step.lift, liftS_mul]
    exact this

  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI : BorelSpace (GA D J.W) := ⟨rfl⟩
  haveI := B.vA.haar
  haveI := s.vW.haar
  obtain ⟨hc, hd, -⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D B.A (GQ B.A) le_rfl

  set f : GA D B.A → GA D J.W → ℂ := fun h₀ h => φ h₀ * (G h * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) with hf
  have hcont : Continuous (Function.uncurry f) := by
    have h2 := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
    rw [← hx] at h2
    have h3 : Continuous fun p : GA D B.A × GA D J.W =>
        (((embA B.d B.o p.1, p.2), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((hemb.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have h4 := h2.comp h3
    simp only [Function.comp_def] at h4
    have h5 : Continuous fun p : GA D B.A × GA D J.W => flatBF s (s.om (embA B.d B.o p.1, p.2) Φ) 0 := by
      simp only [flatBF, flat]
      exact h4
    exact (hφ.2.comp continuous_fst).mul ((hG.2.1.comp continuous_snd).mul h5)
  have hinv := (GlobalTheory.T.unfoldedBesselJacobiKernel_laws D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ).2.2.1
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.unfolded_besselJacobi_integral_abs_le D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS s.vT s.vU s.vW J.d.e
    hb G Φ hG hΦ 𝓑 h𝓑'
  have hint : Integrable (Function.uncurry f) ((B.vA.μ.restrict B.vA.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
    refine GlobalTheory.fubini_compact_quotient (GA D B.A) B.vA.μ (GQ B.A) hc hd B.cpt B.vA.𝓕 B.vA.fund (GA D J.W) _ f
      hcont.measurable (fun γ hγ h x => by simp only [hf, hφ.1 γ hγ, hinv γ hγ]) fun K hK => ?_
    have hq : Continuous fun h₀ => ‖φ h₀‖ * (C * height B.V (embA B.d B.o h₀) ^ A) :=
      hφ.2.norm.mul (continuous_const.mul (((continuous_height B.V).comp hemb).pow A))
    obtain ⟨M, hM⟩ := hK.bddAbove_image hq.continuousOn
    refine ⟨M.toNNReal, fun h₀ hh => ?_⟩
    calc ∫⁻ h in 𝓑, ‖f h₀ h‖ₑ ∂s.vW.μ
        = ‖φ h₀‖ₑ * ∫⁻ h in 𝓑, ‖G h‖ₑ * ‖flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0‖ₑ ∂s.vW.μ := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          simp only [hf, enorm_mul]
      _ ≤ ‖φ h₀‖ₑ * ENNReal.ofReal (C * height B.V (embA B.d B.o h₀) ^ A) := by
          refine mul_le_mul_right (le_trans (lintegral_mono fun h => mul_le_mul_right ?_ _) (hC _)) _
          rw [← hfl]
          exact enorm_fl_le ψ B.d J.W s.vS s.vT s.vU Th hn _ _
      _ = ENNReal.ofReal (‖φ h₀‖ * (C * height B.V (embA B.d B.o h₀) ^ A)) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ M.toNNReal := ENNReal.ofReal_le_ofReal (hM ⟨h₀, hh, rfl⟩)
  have hker : kerBF s φ G Φ = fun h => ∫ h₀ in B.vA.𝓕, f h₀ h ∂B.vA.μ := by
    funext h
    simp only [kerBF, hf]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_left_comm _ _ _)
  rw [hker]
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hint]
  simp only [BesLev.per, besPer, besFun, hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  simp only
  rw [integral_const_mul, ← h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hThd]
  ring

end GlobalTheory.Unf
