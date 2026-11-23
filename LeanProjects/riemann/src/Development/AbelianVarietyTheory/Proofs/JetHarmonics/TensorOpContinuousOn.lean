import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
open Formalism.REAL (qdet GlRel IsHW)

noncomputable section

namespace GlobalTheory.TensorDualStd

section General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k : ℕ}

def tensorOp (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun c => ∑ d, C c d • A (y d)
      map_add' := fun x y => by
        ext c
        simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by
        ext c
        simp [Finset.smul_sum, smul_smul, mul_comm] }

theorem tensorOp_apply (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tensorOp C A y c = ∑ d, C c d • A (y d) := rfl

theorem tensorOp_one : tensorOp (1 : Matrix (Fin k) (Fin k) ℂ) (1 : V →L[ℂ] V) = 1 := by
  ext y c
  simp [tensorOp_apply, Matrix.one_apply]

theorem tensorOp_mul (C D : Matrix (Fin k) (Fin k) ℂ) (A B : V →L[ℂ] V) :
    tensorOp (C * D) (A.comp B) = (tensorOp C A).comp (tensorOp D B) := by
  ext y c
  simp only [tensorOp_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, map_sum,
    map_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem tensorOp_norm {C : Matrix (Fin k) (Fin k) ℂ} (hC : ∀ d e, ∑ c, star (C c d) * C c e = if d = e then 1 else 0)
    {A : V →L[ℂ] V} (hA : ∀ v, ‖A v‖ = ‖v‖) (y : PiLp 2 (fun _ : Fin k => V)) : ‖tensorOp C A y‖ = ‖y‖ := by
  have h1 : inner ℂ (tensorOp C A y) (tensorOp C A y) = inner ℂ y y := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    calc ∑ c, inner ℂ (tensorOp C A y c) (tensorOp C A y c)
        = ∑ c, ∑ d, ∑ e, (star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [tensorOp_apply, sum_inner]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [inner_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [inner_smul_left, inner_smul_right, mul_assoc]
          rfl
      _ = ∑ d, ∑ e, (∑ c, star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ d, inner ℂ (y d) (y d) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [hC, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hA]
  rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]

theorem tensorOp_continuousOn {X : Type} [TopologicalSpace X] {s : Set X} {C : X → Matrix (Fin k) (Fin k) ℂ}
    {A : X → (V →L[ℂ] V)} (hC : ∀ c d, Continuous fun x => C x c d) (hA : ContinuousOn A s) :
    ContinuousOn (fun x => tensorOp (C x) (A x)) s := by
  rw [continuousOn_clm_apply]
  intro y
  have h : ContinuousOn (fun x => fun c => ∑ d, C x c d • A x (y d)) s := by
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    exact (hC c d).continuousOn.smul (hA.clm_apply continuousOn_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin k => V)).comp_continuousOn h

end General

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem herm_inv {h : Mx k r} (hh : h ∈ UWset k r z) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ v) (h *ᵥ w) = herm (Hpk k r) v w := by
  have e : hᴴ * Hpk k r * h = Hpk k r := hh.1
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]

theorem inWb_mulVec {h : Mx k r} (hh : h ∈ UWset k r z) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (h *ᵥ v) := by
  rw [Qx8.inWb_iff] at hv ⊢
  intro c
  have hc := hh.2.1 c
  constructor
  · rw [← Qx8.coord_e (h *ᵥ v) c, ← hc.2, herm_inv hh, Qx8.coord_e]
    exact (hv c).1
  · rw [← Qx8.coord_es (h *ᵥ v) c, ← hc.1, herm_inv hh, Qx8.coord_es]
    exact (hv c).2

theorem expand {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hB : IsFrameOf k r [z] B) {h : Mx k r} (hh : h ∈ UWset k r z) (d : Fin k) :
    h *ᵥ B d = ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) • B c := by
  refine HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB (inWb_mulVec hh (hB.1 d)) ?_
  have h1 := herm_inv hh (B d) z
  rw [hh.2.2] at h1
  rw [h1]
  exact hB.2.2 d z (by simp)

def dualMat (k r : ℕ) (B : Fin k → Fin (2 * r + k + 1) → ℂ) (h : Mx k r) : Matrix (Fin k) (Fin k) ℂ :=
  fun c d => star (herm (Hpk k r) (h *ᵥ B d) (B c))

end GlobalTheory.TensorDualStd

open GlobalTheory.TensorDualStd in

theorem GlobalTheory.tensor_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hn hB
  refine ⟨fun h => tensorOp (dualMat k r B h) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, fun h _ y c => rfl⟩
  · have h1 : dualMat k r B 1 = 1 := by
      ext c d
      simp only [dualMat, Matrix.one_mulVec, hB.2.1, Matrix.one_apply]
      by_cases h : c = d
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [h1, hπ.1.1]
    exact tensorOp_one
  · intro a ha b hb
    have h1 : dualMat k r B (a * b) = dualMat k r B a * dualMat k r B b := by
      ext c d
      simp only [dualMat, Matrix.mul_apply]
      rw [← Matrix.mulVec_mulVec]
      conv_lhs => rw [expand hz hT hB hb d, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
      rw [HermitianFormSums.herm_lsum, star_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [star_mul]
    simp only [h1, hπ.1.2 a ha b hb]
    exact tensorOp_mul _ _ _ _
  · refine tensorOp_continuousOn (fun c d => ?_) hπ.2
    unfold dualMat herm
    fun_prop
  · intro h hh v
    refine tensorOp_norm (fun d e => ?_) (hn h hh) v
    simp only [dualMat, star_star]
    rw [← HermitianFormSums.herm_comb hB, ← expand hz hT hB hh, ← expand hz hT hB hh, herm_inv hh, hB.2.1]

end
