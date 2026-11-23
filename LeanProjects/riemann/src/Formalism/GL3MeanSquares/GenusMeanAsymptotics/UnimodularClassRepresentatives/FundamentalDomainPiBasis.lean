import Mathlib

open NumberField NumberField.mixedEmbedding MeasureTheory Module

open scoped Classical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

def psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    (ι → mixedSpace K) ≃ₗ[ℝ] ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) where
  toFun y := fun w i => (y i).2 w
  invFun z := fun i => (fun w => isEmptyElim w, fun w => z w i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext i
    exact Prod.ext (Subsingleton.elim _ _) rfl
  right_inv z := rfl

theorem psi_apply [IsEmpty {w : InfinitePlace K // w.IsReal}] (y : ι → mixedSpace K)
    (w : {w : InfinitePlace K // w.IsComplex}) (i : ι) : psi K ι y w i = (y i).2 w := rfl

theorem measurePreserving_psi [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (psi K ι) volume volume := by
  let e := (psi K ι).toContinuousLinearEquiv
  have he : ∀ y, e y = psi K ι y := fun y => rfl
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e volume = volume
  have : (Measure.map e volume).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let K₀ : TopologicalSpace.PositiveCompacts
      ({w : InfinitePlace K // w.IsComplex} → ι → ℂ) :=
    ⟨⟨Metric.closedBall 0 1, isCompact_closedBall 0 1⟩, by
      change (interior (Metric.closedBall 0 1)).Nonempty
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, Metric.mem_ball_self one_pos⟩⟩
  have hK₀ : (K₀ : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) = Metric.closedBall 0 1 := rfl
  rw [Measure.addHaarMeasure_unique (Measure.map e volume) K₀,
    Measure.addHaarMeasure_unique (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) K₀]
  congr 1
  rw [hK₀, Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet]
  have h1 : e ⁻¹' Metric.closedBall 0 1 = Set.pi Set.univ fun _ : ι =>
      (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) ×ˢ
        Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) 1 := by
    ext y
    simp only [Set.mem_preimage, mem_closedBall_zero_iff, he, Set.mem_pi, Set.mem_univ,
      Set.mem_prod, true_and, forall_true_left, pi_norm_le_iff_of_nonneg zero_le_one, psi_apply]
    exact forall_comm
  have h2 : (Metric.closedBall 0 1 : Set ({w : InfinitePlace K // w.IsComplex} → ι → ℂ)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_closedBall_zero_iff, Set.mem_pi, Set.mem_univ, forall_true_left,
      pi_norm_le_iff_of_nonneg zero_le_one]
  have h3 : volume (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  rw [h1, h2, volume_pi_pi, volume_pi_pi]
  simp only [volume_pi_pi, Measure.volume_eq_prod, Measure.prod_prod, h3, one_mul]
  exact Finset.prod_comm

def piBasis : Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (ι → mixedSpace K) :=
  Pi.basis fun _ => latticeBasis K

theorem fundamentalDomain_piBasis : ZSpan.fundamentalDomain (piBasis K ι) =
    Set.pi Set.univ fun _ => ZSpan.fundamentalDomain (latticeBasis K) := by
  ext y
  simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies, forall_const, piBasis,
    Pi.basis_repr, Sigma.forall]

theorem mem_span_piBasis (y : ι → mixedSpace K) :
    y ∈ Submodule.span ℤ (Set.range (piBasis K ι)) ↔
      ∀ i, ∃ a : 𝓞 K, mixedEmbedding K (algebraMap (𝓞 K) K a) = y i := by
  simp only [Basis.mem_span_iff_repr_mem ℤ, piBasis, Pi.basis_repr, Sigma.forall]
  refine forall_congr' fun i => ?_
  refine (Basis.mem_span_iff_repr_mem ℤ (latticeBasis K) (y i)).symm.trans ?_
  rw [mem_span_latticeBasis]
  simp [NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]

theorem covolume_piBasis :
    ZLattice.covolume (Submodule.span ℤ (Set.range (piBasis K ι))) volume =
      ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (piBasis K ι) volume),
    measureReal_def, fundamentalDomain_piBasis, volume_pi_pi, ENNReal.toReal_prod, Finset.prod_const,
    Finset.card_univ, ← measureReal_def,
    ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (latticeBasis K) volume),
    span_latticeBasis, covolume_integerLattice]

end Formalism.HermitianLattices.Ext.L3.BallC
