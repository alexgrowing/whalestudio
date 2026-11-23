import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValuesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.StepExists

set_option maxHeartbeats 1000000 in

theorem stepEx : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' ω f hpre
  obtain ⟨X, hX, -, -, hX3, hX4, hX5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties h1 h2
  have I : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries h1 h2 h3 h4 D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X I (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X I (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X I (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X I)))
  have hrule : ∀ τ, RulePar X (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) := fun τ =>
    ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions h1 h2 D c.t _ _ _ _ (hpre.par τ)).2 X hX3 hX4 hX5).1
  have hwe : IsWeilExp c.ψ s.V s'.V (c.a k) (c.a k) ω :=
    ⟨c.χ k, c.χ k, hpre.weil, fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair h1 h2 D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf
    hpre.par).1
  have hItW := hIt ω f hwe hpre.vac
  have hL := hPL s.par s'.par (c.a k) (c.a k) hrule s.V s'.V s.M s'.M c.θ c.ψ hc.inf ω hwe f It hpre.vac hItW
    s'.ν s'.fd hs'.haar hs'.fund f (isVacF_of_isVacVec hpre.vac)

  have hlev : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v h,
      IntegrableOn (fun g => thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) *
        (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g) s'.fd s'.ν ∧
      ∫ g in s'.fd, thetaKO ω h g (ptOf c.ψ c.θ s.M s'.M f φ) * (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v g ∂s'.ν =
        u (It φ v) h := by
    intro F
    obtain ⟨F', hF', hint⟩ := hL _ (GlobalTheory.ChainOnto.multT_le_noLevel c.θ s'.M _ _ F.2)
    refine ⟨F', ?_, hint⟩
    have hlaw : ∀ P v, ∀ κ ∈ s.J, ∀ g, F' (It P v) (g * κ) = F' (It P v) g := by
      intro P v κ hκ g
      rw [← (hint P v (g * κ)).2, ← (hint P v g).2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
      have hm : ((g * κ, g') : GA D s.V × GA D s'.V) = (g, g') * (κ, 1) := by simp
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, hpre.law P κ hκ 1 (one_mem _)]
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s.V s.par s.M c.θ hc.inf _ _ (fun κ hκ => hs.fin hκ) F' hF' ?_
    intro w hw κ hκ g
    have hx := GlobalTheory.T.kFiniteSpan_le_span_realIntertwiner_values h1 h2 D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.a k) (c.a k) ω f It hc.inf hwe
      hpre.vac hItW hw
    suffices e : F' w (g * κ) = F' w g by rw [e]; simp
    clear hw
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨P, v, _, rfl⟩ := hx; exact hlaw P v κ hκ g
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]

  let pt : PolF D s'.V.rank s.V.rank →ₗ[ℂ] (WO s.V s'.V → ℂ) :=
    pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f
  have hp : ptOf c.ψ c.θ s.M s'.M f = pt := rfl
  have hint : ∀ F : s'.CC c, ∀ φ v g, IntegrableOn (fun h => (LinearMap.proj 0 ∘ₗ ω (g, h)) (pt φ) *
      (F : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) v h) s'.fd s'.ν := fun F φ v g => by
    obtain ⟨u, -, hu⟩ := hlev F
    exact (hu φ v g).1
  obtain ⟨B, hB⟩ := GlobalTheory.Chain.IoLift.exists_trilinear s'.ν s'.fd (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt
    (s'.CC c) hint
  have hex : ∀ F : s'.CC c, ∃ u ∈ s.CC c, ∀ φ v, u (It φ v) = B φ v F := fun F => by
    obtain ⟨u, hu, he⟩ := hlev F
    refine ⟨u, hu, fun φ v => ?_⟩
    rw [hB]
    funext g
    exact ((he φ v g).2).symm
  have hun : ∀ u ∈ s.CC c, (∀ φ v, u (It φ v) = 0) → u = 0 := fun u hu h0 => by
    obtain ⟨φ, v, hne⟩ : ∃ φ v, It φ v ≠ 0 := by
      by_contra hn
      exact hItW.ne (LinearMap.ext₂ fun φ v => by_contra fun h => hn ⟨φ, v, h⟩)
    exact GlobalTheory.Grid.Sep.multT_eq_zero hu hne (h0 φ v)
  obtain ⟨io, hio⟩ := GlobalTheory.Chain.IoLift.ioExists_of_forall (T := It) (C' := s.CC c) hint B hB hex hun
  exact ⟨⟨ω, f, It, io⟩, rfl, rfl, ⟨hpre, hItW, hio⟩⟩

end GlobalTheory.EvenOnto.StepExists
