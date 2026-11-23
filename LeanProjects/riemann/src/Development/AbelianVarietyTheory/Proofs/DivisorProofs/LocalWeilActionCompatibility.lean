import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem locOp_weil_rho : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (g : UA σ X.J) (h : UA σ W.J), g ∈ UAt σ X (evFin F v) →
    h ∈ UAt σ W (evFin F v) → ∀ (w : Matrix (Fin n) (Fin d) (AE F E)), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      locOp v (om (g, h)) (locOp v (M.co.rho B.ψ (partFin v w)) φ) =
        locOp v (M.co.rho B.ψ (partFin v (mat g * w * (mat h)ᵀ))) (locOp v (om (g, h)) φ) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v g h hg hh w φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hK
  have hψ : Continuous B.ψ := hP.base.std.1
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨R, h0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  have hact : actAB (cA σ) (g, h) (partFin v w) = partFin v (mat g * w * (mat h)ᵀ) := by
    show mat g * (GlobalTheory.LatVac.liftV v 1 • w) * (mat h)ᵀ = GlobalTheory.LatVac.liftV v 1 • (mat g * w * (mat h)ᵀ)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hψ₁ := locOp_mem v (M.co.rho B.ψ (partFin v w)) φ
  have hψ₂ := locOp_mem v (om (g, h)) φ
  have key : tens (evFin F v) (locOp v (om (g, h)) (locOp v (M.co.rho B.ψ (partFin v w)) φ)) R =
      tens (evFin F v) (locOp v (M.co.rho B.ψ (partFin v (mat g * w * (mat h)ᵀ))) (locOp v (om (g, h)) φ)) R := by
    rw [← acts_locOp_om hA hP hg hh hψ₁ R (hR _ hψ₁), ← (locOp_rho M.co hψ v w hφ).1 R (hR _ hφ),
      hS.impl (g, h) _ _ (hR _ hφ).2, hact, acts_locOp_om hA hP hg hh hφ R (hR _ hφ),
      (locOp_rho M.co hψ v (mat g * w * (mat h)ᵀ) hψ₂).1 R (hR _ hψ₂)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
  have e := congrFun key fun i => GlobalTheory.LatVac.liftV v (t i)
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hrz] at e
  exact mul_right_cancel₀ h0 e

end GlobalTheory.ThK.LemF

end
