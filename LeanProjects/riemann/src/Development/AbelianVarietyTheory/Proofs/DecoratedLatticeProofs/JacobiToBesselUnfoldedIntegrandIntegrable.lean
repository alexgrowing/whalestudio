import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FubiniCompactQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpecStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem quasiFam_bdd_on_compact {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S L : HSp D}
    (v : VolM D L.rank S.rank) {Y : GA D S → WO S L → ℂ} (hY : IsQuasiFam ψ S L Y) {K : Set (GA D S)}
    (hK : IsCompact K) : ∃ M : ℝ, ∀ h ∈ K, ∀ w, ‖Y h w‖ ≤ M := by
  set Kf : Mx D L.rank S.rank → GA D S → ℂ := fun x p => ((‖Y p x‖ : ℝ) : ℂ) with hKf
  have hc : Continuous (Function.uncurry Kf) :=
    Complex.continuous_ofReal.comp (continuous_norm.comp (hY.cont.comp continuous_swap))
  have hper : ∀ γ ∈ ratMx D L.rank S.rank, ∀ x p, Kf (γ + x) p = Kf x p := by
    rintro γ ⟨γ', rfl⟩ x p
    have hq := hY.quasi p γ' x
    have h1 : (incA D).toAddMonoidHom.mapMatrix γ' = ratW L S γ' := rfl
    simp only [hKf, h1, hq, norm_mul, hψ.1.2.1, one_mul]
  obtain ⟨-, -, hloc, -⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D L.rank S.rank v (GA D S) Kf hc hper
  choose C hC using hloc
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun p => {q | ∀ x, ‖Kf x q‖ ≤ C p}) (fun p _ => hC p)
  refine ⟨∑ p ∈ t, |C p|, fun h hh w => ?_⟩
  obtain ⟨p, hp, hhp⟩ := Set.mem_iUnion₂.1 (hcov hh)
  have := hhp w
  simp only [hKf, Complex.norm_real, Real.norm_eq_abs, abs_norm] at this
  exact this.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun p => |C p|) (fun _ _ => abs_nonneg _) hp))

theorem unfolded_integrable : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → Integrable (Function.uncurry fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ((J.v0.μ.restrict J.v0.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  haveI := J.v0.haar
  haveI := s.vW.haar
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  obtain ⟨-, -, hvb, -⟩ := GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D
  obtain ⟨vb⟩ := hvb (σ + 1) J.W₀.rank
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.unfolded_besselJacobi_integral_abs_le D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS vb s.vU s.vW x₀
    hbase G Φ hG hΦ 𝓑 h𝓑'
  obtain ⟨hΓc, hΓd, -⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W₀ (GQ J.W₀) le_rfl
  refine GlobalTheory.fubini_compact_quotient (GA D J.W₀) J.v0.μ (GQ J.W₀) hΓc hΓd J.cpt J.v0.𝓕 J.v0.fund (GA D B.V)
    (s.vW.μ.restrict 𝓑) (fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ?_ ?_ ?_
  · exact ((hG.2.1.comp continuous_snd).mul hcont).measurable
  · intro γ hγ h x
    simp only [hinv γ hγ h x]
  · intro K hK
    obtain ⟨M, hM⟩ := quasiFam_bdd_on_compact s.weil.std vL hY hK
    obtain ⟨c, hc⟩ := hK.bddAbove_image
      ((continuous_const.mul ((continuous_height J.W).pow A)).comp J.d.continuous_embed).continuousOn
    refine ⟨M.toNNReal * c.toNNReal, fun h₀ hh₀ => ?_⟩
    have hc' : C * height J.W (J.d.emb0 h₀) ^ A ≤ c := hc ⟨h₀, hh₀, rfl⟩
    calc ∫⁻ h, ‖G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)‖ₑ ∂(s.vW.μ.restrict 𝓑)
        ≤ ∫⁻ h in 𝓑, ENNReal.ofReal M * (‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
            ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 h₀, h) Φ) ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ u.1.1)
              ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν) ∂s.vW.μ := by
          refine lintegral_mono fun h => ?_
          rw [enorm_mul, mul_left_comm]
          have := (GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing D ψ σ J B s vb vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) (quasi_of_fam hY h₀)
            (s.weil.om_pres _ _ hΦ)).2 M (hM h₀ hh₀)
          rw [hx₀]
          gcongr
      _ = ENNReal.ofReal M * ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
            ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 h₀, h) Φ) ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ u.1.1)
              ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν ∂s.vW.μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal c :=
          by gcongr; exact (hCA (J.d.emb0 h₀)).trans (ENNReal.ofReal_le_ofReal hc')
      _ = ((M.toNNReal * c.toNNReal : NNReal) : ENNReal) := by
          rw [ENNReal.coe_mul]; rfl

end GlobalTheory.Unf.FB
