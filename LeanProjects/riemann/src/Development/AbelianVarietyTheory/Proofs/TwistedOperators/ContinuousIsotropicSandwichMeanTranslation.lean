import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoMean

theorem isThetaFunO_bounded {D : D7} (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := hF.quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ') = ratW W V γ' := rfl
  rw [e] at hx
  have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ') x))
  have := hC _ hx
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem continuous_emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (emb V W P Q) := by
  unfold emb
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_meanX : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  intro D V W a b P Q ψ hψ μ 𝓨 hμ F hF
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : FirstCountableTopology (WO V W) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := isThetaFunO_bounded V W ψ hψ F hF
  unfold meanX
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_) (integrable_const C) ?_
  · exact (hF.cont.comp ((continuous_emb V W P Q).add continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hC _
  · exact Filter.Eventually.of_forall fun y => hF.cont.comp (continuous_const.add continuous_id)

end GlobalTheory.IsoMean

end
