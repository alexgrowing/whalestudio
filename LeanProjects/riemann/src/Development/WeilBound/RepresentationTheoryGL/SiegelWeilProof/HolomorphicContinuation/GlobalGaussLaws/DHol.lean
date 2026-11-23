import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferentiableOnAvg

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open DHolH

theorem dHol : DHol := by
  intro hP D n V hn hr θ hθ ν hν P _ _ U hU φ h1 h2 h3 h4 h5
  intro F

  have hfacts : ∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      Continuous M ∧ absThetaInt V ν M < ⊤ ∧ ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N, M, hN, hM, hb⟩ := h5 p₀ z₀ hz₀
    obtain ⟨hMc, hMf⟩ := sch_facts hP V hn hr θ hθ ν hν hM
    exact ⟨N, M, hN, hMc, hMf, hb⟩
  have hcontx : ∀ p, ∀ z ∈ U, Continuous (φ p z) := by
    intro p z hz
    exact (h4 p).comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩
  have hfin : ∀ p, ∀ z ∈ U, absThetaInt V ν (φ p z) < ⊤ := by
    intro p z hz
    obtain ⟨N, M, hN, -, hMf, hb⟩ := hfacts p z hz
    exact lt_of_le_of_lt (absThetaInt_mono V ν (hb (p, z) (mem_of_mem_nhds hN) hz)) hMf
  have hmeas : ∀ p, ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (φ p z))) (autMeasure V ν) :=
    fun p z hz => aestronglyMeasurable_thS V ν (hcontx p z hz) (hfin p z hz)
  have hfam : ∀ p, Fam V ν U (φ p) := by
    intro p
    refine ⟨h2 p, fun z₀ hz₀ => ?_, hmeas p⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p z₀ hz₀
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hv
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hb₂, M, hMc, hMf, ?_⟩
    intro z hz x
    have hzv : z ∈ v := hb₁ (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hzU : z ∈ U := hb₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact hb (p, z) (huv ⟨mem_of_mem_nhds hu, hzv⟩) hzU x
  refine ⟨?_, fun p => ?_, fun p r z hz => ?_⟩
  ·
    rintro ⟨p₀, z₀⟩ ⟨-, hz₀⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p₀ z₀ hz₀
    have hfinq := ae_absTheta_lt V ν hMc hMf
    have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
      intro q hq
      refine Summable.of_enorm ?_
      simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
    have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ =
          (descend (GQ V) (absTheta V M) q).toReal := by
      intro q hq
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
      rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
      simp
    have hs : Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := self_mem_nhdsWithin
    have hNs : N ∩ Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := inter_mem (mem_nhdsWithin_of_mem_nhds hN) hs
    have hint : ContinuousWithinAt (fun pz : P × ℂ => ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν)
        (Set.univ ×ˢ U) (p₀, z₀) := by
      refine continuousWithinAt_of_dominated (bound := fun q => (descend (GQ V) (absTheta V M) q).toReal) ?_ ?_
        (integrable_absTheta_toReal V ν hMc hMf) ?_
      · exact Eventually.mono hs fun pz hpz => hmeas pz.1 pz.2 hpz.2
      · refine Eventually.mono hNs fun pz hpz => ?_
        filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hs' : Summable fun ξ => ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
        calc ‖∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
          _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ := hs'.tsum_le_tsum (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
          _ = _ := htsM q hq
      · filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hon : ContinuousOn (fun pz : P × ℂ => ∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)) (N ∩ Set.univ ×ˢ U) :=
          continuousOn_tsum (fun ξ => (h3 _).mono Set.inter_subset_right) hs1
            (fun ξ pz hpz => hb pz hpz.1 hpz.2.2 _)
        exact (hon.continuousWithinAt ⟨mem_of_mem_nhds hN, ⟨Set.mem_univ _, hz₀⟩⟩).mono_of_mem_nhdsWithin hNs
    have : (fun pz : P × ℂ => F pz.1 pz.2) = fun pz => ((autMeasure V ν) Set.univ).toReal⁻¹ •
        ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν := by
      funext pz
      simp only [F, average_eq]
      rfl
    rw [this]
    exact hint.const_smul ((autMeasure V ν) Set.univ).toReal⁻¹
  · exact differentiableOn_avg V ν hU (hfam p)
  · exact iteratedDeriv_avg V ν hU (hfam p) r z hz

end PositivityTheory.Rg.Sw.Glob
