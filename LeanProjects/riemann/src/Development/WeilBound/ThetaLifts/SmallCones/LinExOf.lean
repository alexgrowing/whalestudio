import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo

theorem linEx_of : LinEx := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW v t
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm model_existence adjoint_statement hB.std h hG M.co
  refine ⟨⟨_, linBar_of_lm adjoint_statement action_uniqueness h hG hι₀⟩, fun x u hx h0 => ?_⟩
  rw [sy, symp_eq h hG hx, ev_sgl, coord_snd.2 h0, dotProduct_zero, sub_zero]
  simp only [coord, dot_ofM, incM_map h, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

end PositivityTheory.ThKCT

end
