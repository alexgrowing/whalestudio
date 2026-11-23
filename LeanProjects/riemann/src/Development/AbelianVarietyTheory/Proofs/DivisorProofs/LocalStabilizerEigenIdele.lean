import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeHeis

open GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul_partFin_shiftA {n d n₁ d₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F) (k : UA σ J)
    (H : Plane E n n₁) (H' : Plane E d d₁) (l : (AE F E)ˣ) (hk : mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x) :
    (mat k * (partFin v (shiftA H H' 1) : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E)) =
      partFin v (shiftA H H' l) := by
  ext i j
  have e := congrFun hk i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
  simp only [partFin, shiftA, Units.val_one, one_smul, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    smul_eq_mul]
  simp only [mul_smul_comm]
  rw [← Finset.smul_sum]
  congr 1
  rw [← mul_assoc, ← e, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => (mul_assoc _ _ _).symm

theorem locOp_rho_om_comm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (k : UA σ G.V.J), k ∈ UAt σ G.V (evFin F v) → ∀ l : (AE F E)ˣ,
      mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) (locOp v (om (k, 1)) φ) =
        locOp v (om (k, 1)) (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1))) φ) := by
  intro hK F E _ _ _ _ _ σ B b a' G H H' X om om' hT v k hk l hkl φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hK.base
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hψ : Continuous B.ψ := hT.base.std.1
  have hS := hT.weil.isUSplitting
  have h1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  set w₁ := partFin v (shiftA (F := F) H H' 1) with hw₁
  set w := partFin v (shiftA (F := F) H H' l) with hw
  set ψ₁ := locOp v (om (k, 1)) φ with hψ₁
  set χ₁ := locOp v (G.M.co.rho B.ψ w₁) φ with hχ₁
  have aT1 : Acts (evFin F v) (om (k, 1)) φ ψ₁ := acts_locOp_om hA hP hk h1 hφ
  have aT2' : Acts (evFin F v) (G.M.co.rho B.ψ w₁) φ χ₁ := (locOp_rho G.M.co hψ v _ hφ).1
  have hχ₁m : χ₁ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) := locOp_mem v _ φ
  have hψ₁m : ψ₁ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) := locOp_mem v _ φ
  have aT2 : Acts (evFin F v) (G.M.co.rho B.ψ w) ψ₁ (locOp v (G.M.co.rho B.ψ w) ψ₁) :=
    (locOp_rho G.M.co hψ v _ hψ₁m).1
  have aT1' : Acts (evFin F v) (om (k, 1)) χ₁ (locOp v (om (k, 1)) χ₁) := acts_locOp_om hA hP hk h1 hχ₁m
  refine GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr => ?_
  have rψ : Rest (evFin F v) ψ₁ r := ⟨hr.1, by rw [← aT1 r hr]; exact hS.pres (k, 1) _ hr.2⟩
  have rχ : Rest (evFin F v) χ₁ r :=
    ⟨hr.1, by rw [← aT2' r hr]; exact GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hT.base.std _ _ hr.2⟩
  rw [← aT2 r rψ, ← aT1 r hr, ← aT1' r rχ, ← aT2' r hr, hS.impl (k, 1) w₁ _ hr.2]
  congr 2
  have e1 : ((((1 : UA σ G.W.J) : GL (Fin (b + 2 + a')) (AE F E)) : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (AE F E))) = 1 := rfl
  simp only [actAB, e1, Matrix.transpose_one, Matrix.mul_one]
  exact (mat_mul_partFin_shiftA v k H H' l hkl).symm

end GlobalTheory.ConeHeis
