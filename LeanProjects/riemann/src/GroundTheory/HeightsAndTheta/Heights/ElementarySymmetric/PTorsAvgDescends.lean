import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace TorsAvgDescends

open RigSymForm

lemma intVec_add {g : ℕ} (u v : Fin g → ℤ) : intVec (u + v) = intVec u + intVec v := by
  funext i; simp [intVec]

lemma intVec_zero {g : ℕ} : intVec (0 : Fin g → ℤ) = 0 := by
  funext i; simp [intVec]

lemma intVec_smul {g : ℕ} (m : ℕ) (u : Fin g → ℤ) : intVec ((m : ℤ) • u) = (m : ℂ) • intVec u := by
  funext i; simp [intVec]

lemma intVec_dot {g : ℕ} (u v : Fin g → ℤ) : intVec u ⬝ᵥ intVec v = ((u ⬝ᵥ v : ℤ) : ℂ) := by
  simp [intVec, dotProduct]

variable (P : RigSymForm ℂ)

lemma latVec_add (u₁ v₁ u₂ v₂ : Fin P.g → ℤ) :
    P.latVec (u₁ + u₂) (v₁ + v₂) = P.latVec u₁ v₁ + P.latVec u₂ v₂ := by
  simp only [latVec, intVec_add, mulVec_add]; abel

lemma latVec_smul (m : ℕ) (u v : Fin P.g → ℤ) :
    P.latVec ((m : ℤ) • u) ((m : ℤ) • v) = (m : ℂ) • P.latVec u v := by
  simp only [latVec, intVec_smul, mulVec_smul, smul_add]

lemma latVec_zero_left (v : Fin P.g → ℤ) : P.latVec 0 v = intVec v := by
  simp [latVec, intVec_zero]

lemma latVec_zero_right (u : Fin P.g → ℤ) : P.latVec u 0 = P.pt.τ *ᵥ intVec u := by
  simp [latVec, intVec_zero]

lemma autL_zero_left (N : ℕ) (v : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL N 0 v w = perFactor P.ch N v := by
  simp [autL, autFactor, intVec_zero]

lemma autL_zero_right (N : ℕ) (u : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL N u 0 w = autFactor P.pt P.ch N u w := by
  simp [autL, perFactor, intVec_zero]

lemma autL_ne_zero (N : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : P.autL N u v w ≠ 0 := by
  unfold autL perFactor autFactor
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

lemma autL_differentiable (N : ℕ) (u v : Fin P.g → ℤ) : Differentiable ℂ (P.autL N u v) := by
  unfold autL autFactor
  simp only [dotProduct]
  fun_prop

lemma section_latVec {n : ℕ} {f : P.Fn} (hf : f ∈ thetaSec P.pt P.ch n) (u v : Fin P.g → ℤ)
    (w : Fin P.g → ℂ) : f (w + P.latVec u v) = P.autL n u v w * f w := by
  obtain ⟨-, h1, h2⟩ := hf
  rw [latVec, show w + (intVec v + P.pt.τ *ᵥ intVec u) = (w + P.pt.τ *ᵥ intVec u) + intVec v by abel,
    h1, h2, autL]
  ring

lemma autL_cocycle (N : ℕ) (u₁ v₁ u₂ v₂ : Fin P.g → ℤ) (w : Fin P.g → ℂ) :
    P.autL N (u₁ + u₂) (v₁ + v₂) w = P.autL N u₁ v₁ (w + P.latVec u₂ v₂) * P.autL N u₂ v₂ w := by
  have hsym : intVec u₂ ⬝ᵥ P.pt.τ *ᵥ intVec u₁ = intVec u₁ ⬝ᵥ P.pt.τ *ᵥ intVec u₂ := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, P.pt.isSymm.eq]
  unfold autL perFactor autFactor latVec
  simp only [← Complex.exp_add, mul_assoc]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨N * (u₁ ⬝ᵥ v₂), ?_⟩
  simp only [intVec_add, mulVec_add, dotProduct_add, add_dotProduct, hsym, intVec_dot]
  push_cast
  ring

lemma autL_mul (N m : ℕ) (k l : Fin P.g → ℤ) (y : Fin P.g → ℂ) :
    P.autL N ((m : ℤ) • k) ((m : ℤ) • l) ((m : ℂ) • y) = P.autL (N * m ^ 2) k l y := by
  obtain ⟨j, hj⟩ := Int.even_mul_pred_self (m : ℤ)
  have hjC : (m : ℂ) * ((m : ℂ) - 1) = (j : ℂ) + j := by exact_mod_cast hj
  obtain ⟨A, hAd⟩ : ∃ A : ℤ, A = ∑ i, ((P.ch.ε i : ℕ) : ℤ) * l i := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℤ, B = ∑ i, k i * ((P.ch.ε' i : ℕ) : ℤ) := ⟨_, rfl⟩
  have hA : P.ch.a ⬝ᵥ intVec l = (A : ℂ) / 2 := by
    subst hAd; simp only [dotProduct, HalfChar.a, intVec]; push_cast
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have hB : intVec k ⬝ᵥ P.ch.b = (B : ℂ) / 2 := by
    subst hBd; simp only [dotProduct, HalfChar.b, intVec]; push_cast
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  unfold autL perFactor autFactor
  simp only [← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨N * j * (B - A), ?_⟩
  simp only [intVec_smul, mulVec_smul, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    hA, hB]
  push_cast
  linear_combination ((Real.pi : ℂ) * I * N * ((B : ℂ) - A)) * hjC

def term (N m : ℕ) (F : P.Fn) (u v : Fin P.g → ℤ) (z : Fin P.g → ℂ) : ℂ :=
  (P.autL N u v ((m : ℂ) • z))⁻¹ * F (z + (m : ℂ)⁻¹ • P.latVec u v)

lemma torsAvg_eq (N m : ℕ) (F : P.Fn) (z : Fin P.g → ℂ) :
    P.torsAvg N m F z = ((m : ℂ) ^ (2 * P.g))⁻¹ *
      ∑ u : Fin P.g → Fin m, ∑ v : Fin P.g → Fin m, term P N m F (torsIdx u) (torsIdx v) z := rfl

lemma term_differentiable (N m : ℕ) {F : (Fin P.g → ℂ) → ℂ} (hF : Differentiable ℂ F) (u v : Fin P.g → ℤ) :
    Differentiable ℂ (term P N m F u v) := by
  have h0 := autL_differentiable P N u v
  have h1 : Differentiable ℂ (fun z : Fin P.g → ℂ => P.autL N u v ((m : ℂ) • z)) := by fun_prop
  have h2 : Differentiable ℂ (fun z : Fin P.g → ℂ => F (z + (m : ℂ)⁻¹ • P.latVec u v)) := by fun_prop
  exact (h1.inv fun z => autL_ne_zero P N u v _).mul h2

lemma term_periodic {N m : ℕ} (hm : (m : ℂ) ≠ 0) {F : P.Fn}
    (hF : F ∈ thetaSec P.pt P.ch (N * m ^ 2)) (u v k l : Fin P.g → ℤ) (z : Fin P.g → ℂ) :
    term P N m F (u + (m : ℤ) • k) (v + (m : ℤ) • l) z = term P N m F u v z := by
  unfold term
  have e1 : (m : ℂ) • z + P.latVec u v = (m : ℂ) • (z + (m : ℂ)⁻¹ • P.latVec u v) := by
    rw [smul_add, smul_inv_smul₀ hm]
  have e2 : z + (m : ℂ)⁻¹ • P.latVec (u + (m : ℤ) • k) (v + (m : ℤ) • l) =
      (z + (m : ℂ)⁻¹ • P.latVec u v) + P.latVec k l := by
    rw [latVec_add, latVec_smul, smul_add, inv_smul_smul₀ hm, add_assoc]
  rw [e2, add_comm u, add_comm v, autL_cocycle, e1, autL_mul, section_latVec P hF]
  have h1 := autL_ne_zero P (N * m ^ 2) k l (z + (m : ℂ)⁻¹ • P.latVec u v)
  rw [mul_inv, mul_assoc, mul_left_comm, inv_mul_cancel_left₀ h1]

lemma term_shift {N m : ℕ} (hm : (m : ℂ) ≠ 0) (F : P.Fn) (u v u₀ v₀ : Fin P.g → ℤ)
    (z : Fin P.g → ℂ) :
    term P N m F u v (z + (m : ℂ)⁻¹ • P.latVec u₀ v₀) =
      P.autL N u₀ v₀ ((m : ℂ) • z) * term P N m F (u + u₀) (v + v₀) z := by
  unfold term
  have e1 : (m : ℂ) • (z + (m : ℂ)⁻¹ • P.latVec u₀ v₀) = (m : ℂ) • z + P.latVec u₀ v₀ := by
    rw [smul_add, smul_inv_smul₀ hm]
  have e2 : z + (m : ℂ)⁻¹ • P.latVec u₀ v₀ + (m : ℂ)⁻¹ • P.latVec u v =
      z + (m : ℂ)⁻¹ • P.latVec (u + u₀) (v + v₀) := by
    rw [latVec_add, smul_add]; abel
  rw [e1, e2, autL_cocycle P N u v u₀ v₀ ((m : ℂ) • z)]
  have h1 := autL_ne_zero P N u v ((m : ℂ) • z + P.latVec u₀ v₀)
  have h2 := autL_ne_zero P N u₀ v₀ ((m : ℂ) • z)
  field_simp

lemma sum_shift {g m : ℕ} (hm : 0 < m) (H : (Fin g → ℤ) → ℂ)
    (hH : ∀ x k, H (x + (m : ℤ) • k) = H x) (s : Fin g → ℤ) :
    ∑ u : Fin g → Fin m, H (torsIdx u + s) = ∑ u : Fin g → Fin m, H (torsIdx u) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  let r : (Fin g → ℤ) → (Fin g → Fin m) := fun x i => ⟨(x i % m).toNat, by
    have := Int.emod_lt_of_pos (x i) hm'; have := Int.emod_nonneg (x i) hm'.ne'; omega⟩
  have hr : ∀ x, H x = H (torsIdx (r x)) := by
    intro x
    have : x = torsIdx (r x) + (m : ℤ) • fun i => x i / m := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, torsIdx, r]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne'), Int.emod_add_mul_ediv]
    conv_lhs => rw [this]
    exact hH _ _
  have hinj : Function.Injective (fun u : Fin g → Fin m => r (torsIdx u + s)) := by
    intro u u' h
    funext i
    have h1 := congrArg Fin.val (congrFun h i)
    simp only [r, Pi.add_apply, torsIdx] at h1
    have e : (((u i : ℕ) : ℤ) + s i) % (m : ℤ) = (((u' i : ℕ) : ℤ) + s i) % m := by
      have := Int.emod_nonneg (((u i : ℕ) : ℤ) + s i) hm'.ne'
      have := Int.emod_nonneg (((u' i : ℕ) : ℤ) + s i) hm'.ne'
      omega
    have e2 : ((u i : ℕ) : ℤ) ≡ ((u' i : ℕ) : ℤ) [ZMOD m] := Int.ModEq.add_right_cancel' (s i) e
    unfold Int.ModEq at e2
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (u i).isLt),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (u' i).isLt)] at e2
    exact Fin.ext (by exact_mod_cast e2)
  exact Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp hinj) _ _ fun u => hr _

end TorsAvgDescends

open TorsAvgDescends RigSymForm

theorem TorsAvgDescends.proof : TorsAvgDescends.Statement := by
  intro P m hm N F hF
  have hF' := P.S_le _ F hF
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hS : P.S N = thetaSec P.pt P.ch N := by rw [← P.span_eq N, Submodule.span_eq]
  have hinv : ∀ u₀ v₀ z, P.torsAvg N m F (z + (m : ℂ)⁻¹ • P.latVec u₀ v₀) =
      P.autL N u₀ v₀ ((m : ℂ) • z) * P.torsAvg N m F z := by
    intro u₀ v₀ z
    have inner : ∀ x : Fin P.g → ℤ, ∑ v : Fin P.g → Fin m, term P N m F x (torsIdx v + v₀) z =
        ∑ v : Fin P.g → Fin m, term P N m F x (torsIdx v) z := fun x =>
      sum_shift hm (fun y => term P N m F x y z) (fun y k => by
        have := term_periodic P hmC hF' x y 0 k z; rwa [smul_zero, add_zero] at this) v₀
    have outer := sum_shift hm (fun x => ∑ v : Fin P.g → Fin m, term P N m F x (torsIdx v) z)
      (fun x k => Finset.sum_congr rfl fun v _ => by
        have := term_periodic P hmC hF' x (torsIdx v) k 0 z; rwa [smul_zero, add_zero] at this) u₀
    have hsum : ∑ u : Fin P.g → Fin m, ∑ v : Fin P.g → Fin m,
        term P N m F (torsIdx u + u₀) (torsIdx v + v₀) z =
        ∑ u : Fin P.g → Fin m, ∑ v : Fin P.g → Fin m, term P N m F (torsIdx u) (torsIdx v) z :=
      (Finset.sum_congr rfl fun u _ => inner _).trans outer
    rw [torsAvg_eq, torsAvg_eq]
    simp only [term_shift P hmC, ← Finset.mul_sum]
    rw [hsum]; ring
  have hd : Differentiable ℂ (P.torsAvg N m F) := by
    rw [show P.torsAvg N m F = fun z => ((m : ℂ) ^ (2 * P.g))⁻¹ * ∑ u : Fin P.g → Fin m,
      ∑ v : Fin P.g → Fin m, term P N m F (torsIdx u) (torsIdx v) z from funext (torsAvg_eq P N m F)]
    exact (Differentiable.fun_sum fun u _ => Differentiable.fun_sum fun v _ =>
      term_differentiable P N m hF'.1 _ _).const_mul _
  refine ⟨fun w => P.torsAvg N m F ((m : ℂ)⁻¹ • w), ?_, fun z => by simp only [inv_smul_smul₀ hmC]⟩
  rw [hS]
  have hd' : Differentiable ℂ (fun w : Fin P.g → ℂ => P.torsAvg N m F ((m : ℂ)⁻¹ • w)) :=
    hd.comp (differentiable_id.const_smul ((m : ℂ)⁻¹))
  refine ⟨hd', fun v w => ?_, fun u w => ?_⟩
  · have := hinv 0 v ((m : ℂ)⁻¹ • w)
    rw [smul_inv_smul₀ hmC, autL_zero_left, latVec_zero_left] at this
    simpa only [smul_add] using this
  · have := hinv u 0 ((m : ℂ)⁻¹ • w)
    rw [smul_inv_smul₀ hmC, autL_zero_right, latVec_zero_right] at this
    simpa only [smul_add] using this

end

end GroundTheory.Heights₂.Heights.KeyFormula
