import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr
open GlobalTheory.Doubling (absE)

theorem unipEx_of : UnipEx := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have G := PositivityTheory.ThKEnd.Grp.unipGood hB.cm (hY.imp (·.herm) (·.skew)) (det_ne hY)
    ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, (h.isUnit_det (det_ne hY).isUnit).ne_zero⟩
  refine ⟨G.ex, G.cov, G.closed, G.right, ?_, fun u hu => ⟨(mem_unip.1 hu).1, ?_⟩, ?_⟩
  · choose m h1 h2 using exists_levi hB.cm h
    let lev : (AE F E)ˣ × UA σ Y₁.J →* UA σ Y.J := MonoidHom.mk' (fun z => m z.1 z.2)
      fun a b => levi_uniq h (h1 _ _) (levi_mul (h1 _ _) (h1 _ _))
    have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have c1 : Continuous fun z => mat (lev z) := by
      have e : (fun z => mat (lev z)) = fun z => _ := funext fun z => h2 z.1 z.2
      rw [e]
      refine (continuous_const.matrix_mul (continuous_matrix fun i j => ?_)).matrix_mul continuous_const
      rcases i with i | i <;> rcases j with j | j
      · exact (PositivityTheory.ThKEnd.Grp.continuous_mat.comp continuous_snd).matrix_elem i j
      · exact continuous_const
      · exact continuous_const
      · fin_cases i <;> fin_cases j
        exacts [Units.continuous_val.comp continuous_fst, continuous_const, continuous_const,
          hc.comp (Units.continuous_coe_inv.comp continuous_fst)]
    refine ⟨lev, Continuous.subtype_mk (f := fun z => (lev z).1) (Units.continuous_iff.2 ⟨c1, ?_⟩) _, h1,
      fun t g p hp => levi_uniq h hp (h1 t g)⟩
    have e : (fun z => mat (lev z)⁻¹) = (fun z => mat (lev z)) ∘ fun z => z⁻¹ := funext fun z => by simp
    exact (e ▸ c1.comp continuous_inv : Continuous fun z => mat (lev z)⁻¹)
  · exact h.ad.fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm) u.2 (mem_unip.1 hu).1
  · obtain ⟨t, ht⟩ : ∃ t, absE F E t = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := ⟨_, GlobalTheory.Eis.Conv.absE_halfE F E σ hB.cm⟩
    refine ⟨t⁻¹, ?_⟩
    rw [map_inv, ht, inv_inv, NNReal.coe_pow]
    exact one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

end PositivityTheory.ThKCT

end
