import Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem stabDec_of : StabDec := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have e : fr (incM F H.ι) (incV F H.x) (incV F H.y) = incM F (fr H.ι H.x H.y) := fr_map _
  refine ⟨fun p t hp => ?_, fun ξ g₁ hg m hm => ?_, fun t g₁ m hm u hu => levi_conj hm hu⟩
  · obtain ⟨u, hu, g₁, m, h1, h2, h3⟩ := stab_dec hB.cm h (det_ne hY) p t hp
    refine ⟨u, hu, g₁, m, h1, h2, fun hr => ?_⟩
    obtain ⟨M, hM⟩ := mem_ratU.1 hr
    refine mem_ratU.2 ⟨(A' * M * fr H.ι H.x H.y).toBlocks₁₁, ?_⟩
    rw [h3, hM, e, incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  · obtain ⟨m', h1, h2⟩ := exists_levi hB.cm h (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁
    obtain ⟨M, hM⟩ := mem_ratU.1 hg
    rw [levi_uniq h hm h1]
    refine mem_ratU.2 ⟨fr H.ι H.x H.y * dg M ξ.1 (σ (ξ⁻¹).1) * A', ?_⟩
    rw [h2, hM, e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext (i | i) (j | j)
    · rfl
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · fin_cases i <;> fin_cases j
      exacts [rfl, (map_zero (inclR (F := F) (E := E) (AF F))).symm, (map_zero (inclR (F := F) (E := E) (AF F))).symm, rfl]

end PositivityTheory.ThKCT

end
