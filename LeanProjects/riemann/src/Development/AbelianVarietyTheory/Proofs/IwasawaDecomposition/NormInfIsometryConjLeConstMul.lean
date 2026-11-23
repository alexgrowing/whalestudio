import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem sum_norm_conj_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) :
    ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤
      ((m : ℝ) * m * (∑ i, ∑ k, ‖P i k‖) * (∑ l, ∑ j, ‖Q l j‖)) * ∑ k, ∑ l, ‖A k l‖ := by
  set cP := ∑ i, ∑ k, ‖P i k‖
  set cQ := ∑ l, ∑ j, ‖Q l j‖
  set S := ∑ k, ∑ l, ‖A k l‖
  have hP : ∀ i k, ‖P i k‖ ≤ cP := fun i k =>
    (Finset.single_le_sum (f := fun k => ‖P i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i))
  have hQ : ∀ l j, ‖Q l j‖ ≤ cQ := fun l j =>
    (Finset.single_le_sum (f := fun j => ‖Q l j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l => ∑ j, ‖Q l j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ l))
  have hcP : 0 ≤ cP := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcQ : 0 ≤ cQ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hent : ∀ i j, ‖(P * A * Q) i j‖ ≤ cP * cQ * S := by
    intro i j
    have e : (P * A * Q) i j = ∑ l, ∑ k, P i k * A k l * Q l j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [e]
    calc ‖∑ l, ∑ k, P i k * A k l * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * ‖A k l‖ * ‖Q l j‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans (le_of_eq ?_))
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul]
      _ ≤ ∑ l, ∑ k, cP * ‖A k l‖ * cQ := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hP i k) (norm_nonneg _)) (hQ l j) (norm_nonneg _)
            (mul_nonneg hcP (norm_nonneg _))
      _ = cP * cQ * S := by
          rw [Finset.sum_comm]
          simp only [S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  calc ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤ ∑ _i : Fin m, ∑ _j : Fin m, cP * cQ * S :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem normInf_kap_le : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  intro D V V' I θ hθ
  let K : D.what₂.Tau → ℝ := fun τ =>
    (V'.rank : ℝ) * V'.rank * (∑ i, ∑ k, ‖I.pT τ i k‖) * (∑ l, ∑ j, ‖I.qT τ l j‖)
  have hK : ∀ τ, 0 ≤ K τ := fun τ => by positivity
  refine ⟨∑ τ, K τ, Finset.sum_nonneg fun τ _ => hK τ, fun g => ?_⟩
  unfold normInf
  have key : ∀ τ, (∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g) i j‖ +
      ‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g)⁻¹ i j‖)) ≤
      K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := by
    intro τ
    rw [← map_inv I.kap g, I.infMat_kap hθ, I.infMat_kap hθ]
    simp only [Finset.sum_add_distrib, mul_add]
    exact add_le_add (sum_norm_conj_le _ _ _) (sum_norm_conj_le _ _ _)
  have hS : ∀ τ, 0 ≤ ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := fun τ => by positivity
  calc _ ≤ ∑ τ, K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := Finset.sum_le_sum fun τ _ => key τ
    _ ≤ ∑ τ, (∑ σ, K σ) * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun σ _ => hK σ) (Finset.mem_univ τ)) (hS τ)
    _ = _ := by rw [← Finset.mul_sum]

end GlobalTheory.Mem.Isom
