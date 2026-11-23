import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajC
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajD

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open GlobalTheory.Core.Rk.SW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L

theorem wMaj : WMaj := by
  intro D n V ψ hψ χ hχ hr θ hθ μ hμ' ω hω Φ
  obtain ⟨𝓕, hμ⟩ := hμ'
  refine ⟨GlobalTheory.T.weil_representation_continuity D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ, fun C hC => ?_⟩
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    rwa [κ.apply_symm_apply g] at h
  have hC' : IsCompact (κ.symm '' C) := hC.image (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  obtain ⟨U, hU, hlev⟩ := LWMaj.unifLevel hW hf _ hC'
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.Unf.mixS_support_inBox D ψ₀ hstd (dblSp A) _ V A.rank (GlobalTheory.Core.Rk.SWLaw.dblDec A)
    (GlobalTheory.SchwartzSch.volOf μ 𝓕 hμ) U hU
  have hsupp : ∀ u ∈ {u | ∃ g ∈ C, u = (ω g Φ).1}, ∀ x, u x ≠ 0 → GlobalTheory.Unf.InBox K x := by
    rintro u ⟨g, hg, rfl⟩ x hx
    rw [key] at hx
    exact hbox _ (hlev _ ⟨g, hg, rfl⟩) x 0 hx
  have hdec : ∀ N : ℕ, ∃ B : ℝ, ∀ u ∈ {u | ∃ g ∈ C, u = (ω g Φ).1}, ∀ x,
      ‖u x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ B := by
    intro N
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.Unf.mixS_decay D ψ₀ hstd θ hθ (dblSp A) _ V A.rank (GlobalTheory.Core.Rk.SWLaw.dblDec A)
      (GlobalTheory.SchwartzSch.volOf μ 𝓕 hμ) N
    obtain ⟨B, hB⟩ := LWMaj.unifSob hstd hθ hW hf _ hC' N
    have hne : (C₂ : ℝ≥0∞) * (B : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
    refine ⟨((C₂ : ℝ≥0∞) * (B : ℝ≥0∞)).toReal, ?_⟩
    rintro u ⟨g, hg, rfl⟩ x
    have h := hC₂ (omh (κ.symm g, 1) f) (hW.om_pres _ _ hf) x 0
    change ‖sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) x‖ₑ * _ ≤ _ at h
    have h2 : (C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ₀ θ N (omh (κ.symm g, 1) f) ≤ C₂ * B :=
      mul_le_mul' le_rfl (hB _ ⟨g, hg, rfl⟩)
    rw [key]
    have h3 : ENNReal.ofReal (‖sch ψ₀ A V μ 𝓕 (omh (κ.symm g, 1) f) x‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N) ≤
        (C₂ : ℝ≥0∞) * B := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      exact h.trans h2
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h3
  obtain ⟨M, hM, hle⟩ := LWMaj.adMaj θ hθ K hK _ hsupp hdec
  exact ⟨M, hM, fun g hg x => hle _ ⟨g, hg, rfl⟩ x⟩

end PositivityTheory.Rg.Rsw.L

end
