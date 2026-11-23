import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardModelDualRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

open StandardModelDualRank in

theorem DualStdModelRank.proof : DualStdModelRank.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hrange : Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)) = Set.range (u K i) := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟩, j⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(), j⟩, rfl⟩
  rw [hrange] at hΦ
  refine ⟨?_, ?_⟩
  · change dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i ≠ 0
    exact mul_ne_zero (coord_ne_zero b c) S_ne_zero
  have hr : (fun t : T => dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      fun t => w b t * (w b c)⁻¹ := by
    funext t
    change dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i /
      (dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i) = _
    rw [← div_eq_mul_inv, w, w, mul_div_mul_right (_ * dualStdModelS K i) _ (T_ne_zero (K := K) (i := i))]
  rw [hr]
  let B := Module.finBasis ℚ K
  let M' := Algebra.adjoin Φ₀ (Set.range (embK K i))
  have hM' : Subalgebra.toSubmodule M' = Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) :=
    adjoin_embK_eq_span B Φ₀
  have hfg : (Subalgebra.toSubmodule M').FG := by
    rw [hM']
    exact Submodule.fg_span (Set.finite_range _)
  have hwM' : ∀ t, w b t ∈ M' := fun t => by
    rw [w_eq]
    refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, rfl⟩) ?_
    have hu : u K i j ∈ (algebraMap Φ₀ (dualStdModelField K i)).fieldRange := by
      rw [hΦ]
      exact Subfield.subset_closure ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := RingHom.mem_fieldRange.mp hu
    rw [← hg]
    exact Subalgebra.algebraMap_mem _ g
  have hMM' : Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) ≤ M' := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact Subalgebra.mul_mem _ (hwM' t) (Subalgebra.inv_mem_of_algebraic M' (x := ⟨w b c, hwM' c⟩)
      (IsIntegral.of_mem_of_fg M' hfg _ (hwM' c)).isAlgebraic)
  have hβM : ∀ a, embK K i a ∈ Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) := fun a => by
    obtain ⟨N, hN, n, hn⟩ := exists_int_comb b c a
    have hNΩ : (N : dualStdModelField K i) ≠ 0 := by
      rw [← map_intCast (embK K i)]
      exact (map_ne_zero_iff _ (embK K i).injective).mpr (Int.cast_ne_zero.mpr hN)
    have he : embK K i a =
        algebraMap Φ₀ _ ((N : Φ₀)⁻¹) * ∑ t, (n t : dualStdModelField K i) * (w b t * (w b c)⁻¹) := by
      rw [map_inv₀, map_intCast]
      simp only [← mul_assoc, ← Finset.sum_mul, hn]
      field_simp [w_ne_zero b c]
    rw [he]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ fun t _ =>
      Subalgebra.mul_mem _ (intCast_mem _ _) (Algebra.subset_adjoin ⟨t, rfl⟩))
  have hMeq : Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹)) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
    apply le_antisymm
    · rw [← hM']
      exact fun x hx => hMM' hx
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hβM (B k)
  rw [← Subalgebra.finrank_toSubmodule, hMeq, finrank_span_eq_card (linIndep B Φ₀ hΦ), Fintype.card_fin]

end

end GroundTheory.Heights₂.Heights
