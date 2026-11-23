import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContributeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFramesFirstRelationMeanZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mean_theta_orbit : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hsum : ∀ n : flagN d, HasSum (term ψ d W vS (om (n.1, 1) Ψ)) (om (n.1, 1) Ψ 0) :=
    fun n => (hT _ (hw.om_pres _ _ hΨ)).2.2.2.2
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  have hbd : ∀ n : flagN d, ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤
      ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := fun n => by
    have := hC 1 1 n.1 n.2
    rwa [mul_one] at this
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ M := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hM k hk
  have hpart : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ‖∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ ≤
        M * max (C * (height V 1 * quotHeight W 1) ^ A) 0 := by
    intro S n
    rw [tsum_mul_left, norm_mul]
    refine mul_le_mul (hThb n) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hThb n))
    have h1 : ‖∑' x : S, term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
      enorm_tsum_le_tsum_enorm.trans
        ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans (hbd n))
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [toReal_enorm, ENNReal.toReal_ofReal'] at h2
  have hmeas : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      AEStronglyMeasurable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) := by
    intro S
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset S))
      (f := fun s n => ∑ x ∈ s, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun s => ?_)
      (Filter.Eventually.of_forall fun n => ?_)
    · exact (continuous_finsetSum _ fun x _ => hTh.cont.mul (hcont x.1)).aestronglyMeasurable
    · exact (((hsum n).summable.mul_left (Th n.1)).subtype S).hasSum
  have : IsFiniteMeasure (vN.ν.restrict vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
  have hint : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      Integrable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) :=
    fun S => Integrable.of_bound (hmeas S) _ (Filter.Eventually.of_forall (hpart S))

  have h61 := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E => GlobalTheory.T.dependent_frame_first_column_relation D.host.E W.rank ρ x
  let Sb : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := {x | gramQ W x ≠ gramQ W x₀}
  let Sj : Fin ρ → Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := fun j => {x | gramQ W x = gramQ W x₀ ∧
    ((∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
      ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0)}
  have hpt : ∀ n : flagN d, Th n.1 * om (n.1, 1) Ψ 0 =
      (∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      (∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      ∑ j, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 := by
    intro n
    have hs : Summable fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x := (hsum n).summable.mul_left _
    rw [← ((hsum n).mul_left (Th n.1)).tsum_eq]
    have ht : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
        ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 =
          ∑' x, S.indicator (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x) x := fun S => tsum_subtype S (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x)
    rw [ht, ht, Finset.sum_congr rfl fun j _ => ht (Sj j)]
    rw [← Summable.tsum_finsetSum (fun j _ => hs.indicator _), ← Summable.tsum_add (hs.indicator _) (hs.indicator _),
      ← Summable.tsum_add ((hs.indicator _).add (hs.indicator _)) (summable_sum fun j _ => hs.indicator _)]
    congr 1
    funext x
    by_cases hg : gramQ W x = gramQ W x₀
    · have h1 : x ∉ Sb := fun h => h hg
      rw [Set.indicator_of_notMem h1, zero_add]
      by_cases hl : LinearIndependent D.host.E x.transpose
      · have h2 : x ∈ Orb W x₀ := ⟨hl, hg⟩
        have h3 : ∀ j, x ∉ Sj j := fun j h => (h61 x).1.2 ⟨j, h.2⟩ hl
        rw [Set.indicator_of_mem h2, Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero]
      · have h2 : x ∉ Orb W x₀ := fun h => hl h.1
        obtain ⟨j, hj⟩ := (h61 x).1.1 hl
        rw [Set.indicator_of_notMem h2, zero_add, Finset.sum_eq_single j
          (fun j' _ hj' => Set.indicator_of_notMem (fun h => hj' ((h61 x).2.1 j' j h.2 hj)) _)
          (fun h => (h (Finset.mem_univ j)).elim), Set.indicator_of_mem (show x ∈ Sj j from ⟨hg, hj⟩)]
    · have h1 : x ∈ Sb := hg
      have h2 : x ∉ Orb W x₀ := fun h => hg h.2
      have h3 : ∀ j, x ∉ Sj j := fun j h => hg h.1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
        Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero, add_zero]
  have e1 : ∫ n in vN.𝓝, ∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    GlobalTheory.T.unfolding_only_baseGram_rational_points_contribute D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have e2 : ∀ j, ∫ n in vN.𝓝, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    GlobalTheory.T.dependentFrames_firstRelation_mean_zero D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add ?_ ?_, integral_add ?_ ?_,
    integral_finsetSum _ ?_, e1, Finset.sum_eq_zero fun j _ => e2 j, zero_add, add_zero]
  · exact fun j _ => hint _
  · exact hint _
  · exact hint _
  · exact (hint _).add (hint _)
  · exact integrable_finsetSum _ fun j _ => hint _

end GlobalTheory.Unf
