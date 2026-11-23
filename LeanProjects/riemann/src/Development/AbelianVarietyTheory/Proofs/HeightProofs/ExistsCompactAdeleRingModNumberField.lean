import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleCocompact

variable (F : Type) [Field F] [NumberField F]

theorem exists_bound_sub_integer :
    ∃ C : InfinitePlace F → ℝ, ∀ x : F, ∃ y : 𝓞 F, ∀ v : InfinitePlace F, v (x - y) ≤ C v := by
  classical
  refine ⟨fun v => ∑ i, v (integralBasis F i), fun x => ?_⟩
  refine ⟨∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i, fun v => ?_⟩
  have h : x - ((∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F)
      = ∑ i, ((Int.fract ((integralBasis F).repr x i) : ℚ) : F) * integralBasis F i := by
    conv_lhs => enter [1]; rw [← (integralBasis F).sum_repr x]
    change _ - algebraMap (𝓞 F) F _ = _
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, Int.fract, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  rw [h, ← InfinitePlace.norm_embedding_eq, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, norm_mul, InfinitePlace.norm_embedding_eq v (integralBasis F i), map_ratCast,
    Complex.norm_ratCast]
  refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
  rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
  exact_mod_cast (Int.fract_lt_one _).le

omit [NumberField F] in
theorem properSpace_completion (v : InfinitePlace F) : ProperSpace v.Completion := by
  refine ⟨fun x r => ?_⟩
  have h := InfinitePlace.Completion.isometry_extensionEmbedding v
  rw [← h.preimage_closedBall]
  exact h.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)

theorem exists_compact_infinite :
    ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧
      ∀ a : InfiniteAdeleRing F, ∃ y : 𝓞 F, a - algebraMap F (InfiniteAdeleRing F) y ∈ K := by
  obtain ⟨C, hC⟩ := exists_bound_sub_integer F
  haveI := properSpace_completion F
  refine ⟨Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) (1 + C v),
    isCompact_univ_pi fun v => isCompact_closedBall _ _, fun a => ?_⟩
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (a v) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  obtain ⟨x, hx⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hU
    ⟨a, fun v _ => Metric.mem_ball_self one_pos⟩
  obtain ⟨y, hy⟩ := hC x
  refine ⟨y, fun v _ => ?_⟩
  have h1 : ‖a v - algebraMap F (InfiniteAdeleRing F) x v‖ < 1 := by
    rw [← dist_eq_norm, dist_comm]; exact hx v trivial
  have h2 : ‖algebraMap F (InfiniteAdeleRing F) (x - y) v‖ ≤ C v := by
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
    exact hy v
  have h3 : (a - algebraMap F (InfiniteAdeleRing F) y) =
      (a - algebraMap F (InfiniteAdeleRing F) x) + algebraMap F (InfiniteAdeleRing F) (x - y) := by
    rw [map_sub]; ring
  rw [mem_closedBall_zero_iff, h3]
  exact (norm_add_le (a v - algebraMap F (InfiniteAdeleRing F) x v) _).trans (add_le_add h1.le h2)

theorem isCompact_integral :
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem exists_compact_adele : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  intro F _ _
  obtain ⟨K, hK, hK'⟩ := exists_compact_infinite F
  refine ⟨K ×ˢ {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    hK.prod (isCompact_integral F), fun a => ?_⟩
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a.2
  obtain ⟨y, hy⟩ := hK' (a.1 - algebraMap F (InfiniteAdeleRing F) x)
  refine ⟨x + y, ?_, ?_⟩
  · change a.1 - algebraMap F (InfiniteAdeleRing F) (x + y) ∈ K
    rw [map_add, ← sub_sub]; exact hy
  · change ∀ v, (a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y)) v ∈ v.adicCompletionIntegers F
    have h : a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y) =
        b - algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
      rw [hab, map_add, one_smul]; ring
    rw [h]
    intro v
    exact sub_mem (hb v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y)

end GlobalTheory.AdeleCocompact
