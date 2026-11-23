import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilModelLineActionExistsStatement

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.WeilConjLine

theorem deriv_conj_line : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
      ActsD (evI F) (fun t => om (g * γ (Multiplicative.ofAdd t) * g⁻¹, 1)) (T f) (T f₁) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi γ hγ f hf f₁ hf₁
  obtain ⟨f₂, hsd⟩ := GlobalTheory.T.weil_model_line_action_exists hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil γ hγ f hf
  have e := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₂ f₁).2.2.1 _
    ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₂ f₁).1 _ (fun t => map_zero _) hsd) hf₁
  subst e
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  refine (GlobalTheory.RealLift.actsLaws F _ (T f) (T f₂) (T f₂)).1 _ (fun t => map_zero _) ?_
  intro g' hg' l hl
  have key : ∀ φ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) φ (T φ) →
      om (g, h) (GlobalTheory.WeilM.pureA F φ g') = GlobalTheory.WeilM.pureA F (T φ) g' := by
    intro φ hφ
    have hr : ∀ x z, At (evI F) z → (fun x : Fin n × Fin d → AF F => g' (fun i => (x i).2)) (x + z) =
        (fun x : Fin n × Fin d → AF F => g' (fun i => (x i).2)) x := by
      intro x z hz
      change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
      congr 1
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hφ _ ⟨hr, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
  have hfun : (fun t : ℝ => l (om (g * γ (Multiplicative.ofAdd t) * g⁻¹, 1) (GlobalTheory.WeilM.pureA F (T f) g'))) =
      fun t => (l ∘ₗ om (g, h)) (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.WeilM.pureA F f g')) := by
    funext t
    rw [← key f (hT f), LinearMap.comp_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 3
    exact Prod.ext (by simp only [Prod.fst_mul, inv_mul_cancel_right]) (by simp)
  rw [hfun, ← key f₂ (hT f₂)]
  exact hsd g' hg' _ (hS.adm (g, h) l hl)

end GlobalTheory.WeilConjLine
