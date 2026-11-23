import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaCoefCont

private theorem measure_fundamentalDomain_ratL_lt_infty {D : D7} (V W : HSp D) (ν : Measure (WO V W)) (𝓕 : Set (WO V W))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) : ν 𝓕 < ⊤ := by
  obtain ⟨hg, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI := hg
  haveI := hsc
  haveI := hdisc
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov ν h𝓕

theorem continuous_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  intro D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hfin : ν 𝓕 < ⊤ := measure_fundamentalDomain_ratL_lt_infty V W ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C', hC'⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG'
  obtain ⟨g, hg⟩ : ∃ g : GlobalTheory.RealWeil.BB ψ V W, (g.1 : WO V W → ℂ) = G :=
    ⟨_, GlobalTheory.RealWeil.coe_toB hψ G hG⟩
  have hE : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
    unfold GlobalTheory.IsoMean.emb
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hρ : Continuous fun y : Mx D a b => GlobalTheory.RealWeil.rhoB hψ (GlobalTheory.IsoMean.emb V W P Q y) g :=
    (GlobalTheory.RealWeil.continuous_rhoB hψ g).comp hE

  have hΦ : Continuous fun h : GlobalTheory.RealWeil.BB ψ V W => ∫ u in 𝓕, h.1 u * star (G' u) ∂ν := by
    rw [continuous_iff_continuousAt]
    intro h₀
    have hnear : ∀ᶠ h in nhds h₀, ‖h‖ < ‖h₀‖ + 1 :=
      (continuous_norm.tendsto h₀).eventually (gt_mem_nhds (lt_add_one _))
    refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => (‖h₀‖ + 1) * C') ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun h =>
        (h.1.continuous.mul (continuous_star.comp hG'.cont)).aestronglyMeasurable
    · refine hnear.mono fun h hh => Filter.Eventually.of_forall fun u => ?_
      rw [norm_mul, norm_star]
      exact mul_le_mul ((GlobalTheory.RealWeil.norm_ev_le u h).trans hh.le) (hC' u) (norm_nonneg _)
        ((norm_nonneg h).trans hh.le)
    · exact integrable_const _
    · refine Filter.Eventually.of_forall fun u => ?_
      have hev : Continuous fun h : GlobalTheory.RealWeil.BB ψ V W => h.1 u := by
        have hc : Continuous fun h : GlobalTheory.RealWeil.BB ψ V W => GlobalTheory.RealWeil.ev _ _ u h :=
          (GlobalTheory.RealWeil.ev _ _ u).continuous
        simpa only [GlobalTheory.RealWeil.ev_apply] using hc
      exact (hev.mul continuous_const).continuousAt
  have key : ∀ (y : Mx D a b) (u : WO V W), heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u =
      (GlobalTheory.RealWeil.rhoB hψ (GlobalTheory.IsoMean.emb V W P Q y) g).1 u := by
    intro y u
    rw [GlobalTheory.RealWeil.coe_rhoB, hg]
  simp_rw [key]
  exact hΦ.comp hρ

end GlobalTheory.ThetaCoefCont

end
