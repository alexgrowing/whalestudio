import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.RhoConj

theorem rho_om_comm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (h : UA σ W.J),
    h ∈ UAt σ W (evFin F v) → ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      locOp v (M.co.rho B.ψ z) (locOp v (om (1, h)) φ) = locOp v (om (1, h)) (locOp v (M.co.rho B.ψ (z * (mat h⁻¹)ᵀ)) φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v h hh z hz φ hφ
  have hA := GlobalTheory.T.theta_action_exists hPr
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hw : At (evFin F v) (z * (mat h⁻¹)ᵀ) := fun u hu => by rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At (evFin F v) (mat (1 : UA σ X.J) - 1)
    intro u _
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  have hact : actAB (cA σ) ((1 : UA σ X.J), h) (z * (mat h⁻¹)ᵀ) = z := by
    show mat (1 : UA σ X.J) * (z * (mat h⁻¹)ᵀ) * (mat h)ᵀ = z
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, GlobalTheory.StabHaar.mat_mul_inv,
      Matrix.transpose_one, Matrix.mul_one]
  have aom : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) ψ (locOp v (om (1, h)) ψ) :=
    fun ψ hψ => acts_locOp_om hA hP h1 hh hψ
  have arho : ∀ u, At (evFin F v) u → ∀ ψ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ u) ψ (locOp v (M.co.rho B.ψ u) ψ) :=
    fun u hu ψ hψ => acts_locOp ((hA F E σ B n d X W M χX χW om r s r' s' hP v).2.1 u hu ψ hψ).exists
  obtain ⟨R, h0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  have key : tens (evFin F v) (locOp v (M.co.rho B.ψ z) (locOp v (om (1, h)) φ)) R =
      tens (evFin F v) (locOp v (om (1, h)) (locOp v (M.co.rho B.ψ (z * (mat h⁻¹)ᵀ)) φ)) R := by
    rw [← arho z hz _ (locOp_mem _ _ _) R (hR _ (locOp_mem _ _ _)), ← aom _ (locOp_mem _ _ _) R (hR _ (locOp_mem _ _ _)),
      ← aom φ hφ R (hR φ hφ), ← arho _ hw φ hφ R (hR φ hφ), hS.impl _ _ _ (hR φ hφ).2, hact]
  funext t
  have hzL : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by simpa using (hR φ hφ).1 0 _ hzL
  have e := congrFun key fun i => GlobalTheory.LatVac.liftV v (t i)
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hrz] at e
  exact mul_right_cancel₀ h0 e

end GlobalTheory.ThK.LemF.RhoConj
