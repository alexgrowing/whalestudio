import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.LossBoundNonneg

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

section sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem good_congr {D : ℕ} {Q₁ Q₂ : B.Mat k r → ℂ} (h : ∀ g, Q₁ g = Q₂ g) (h₁ : Good D Q₁) : Good D Q₂ := by
  have : Q₁ = Q₂ := funext h
  exact this ▸ h₁

theorem good_mono {a b : ℕ} (hab : a ≤ b) (Q : B.Mat k r → ℂ) (h : Good a Q) : Good b Q := by
  refine ⟨h.1, fun ops hl => ?_⟩
  obtain ⟨C, hC⟩ := h.2 ops hl
  refine ⟨max C 0, fun g hg => (hC g hg).trans ?_⟩
  have h1 := one_le_gN g hg
  calc C * B.gN g ^ a ≤ max C 0 * B.gN g ^ a :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
    _ ≤ max C 0 * B.gN g ^ b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hab) (le_max_right _ _)

theorem good_add {D : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good D Q₁) (h₂ : Good D Q₂) :
    Good D (fun g => Q₁ g + Q₂ g) := by
  refine ⟨h₁.1.add h₂.1, fun ops hl => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.2 ops hl
  obtain ⟨C₂, hC₂⟩ := h₂.2 ops hl
  refine ⟨C₁ + C₂, fun g hg => ?_⟩
  rw [apO_add ops hl Q₁ Q₂ (smooth_ck Q₁ h₁.1) (smooth_ck Q₂ h₂.1) g hg]
  have e1 := hC₁ g hg
  have e2 := hC₂ g hg
  calc _ ≤ ‖apO ops Q₁ g‖ + ‖apO ops Q₂ g‖ := norm_add_le _ _
    _ ≤ C₁ * B.gN g ^ D + C₂ * B.gN g ^ D := add_le_add e1 e2
    _ = (C₁ + C₂) * B.gN g ^ D := by ring

theorem good_mul {a b : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good a Q₁) (h₂ : Good b Q₂) :
    Good (a + b) (fun g => Q₁ g * Q₂ g) := by
  refine ⟨h₁.1.mul h₂.1, fun ops hl => ?_⟩
  have hterm : ∀ p ∈ splits ops, ∃ C, ∀ g ∈ B.GV k r,
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖ ≤ C * B.gN g ^ (a + b) := by
    intro p hp
    obtain ⟨s1, s2⟩ := mem_splits _ p hp
    obtain ⟨C₁, hC₁⟩ := h₁.2 p.1 (fun o ho => hl o (s1.subset ho))
    obtain ⟨C₂, hC₂⟩ := h₂.2 p.2 (fun o ho => hl o (s2.subset ho))
    refine ⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩
    rw [norm_smul, pow_add]
    have hN : 0 ≤ B.gN g := (gN_pos g hg).le
    have e1 : ‖apO p.1 Q₁ g‖ ≤ max C₁ 0 * B.gN g ^ a :=
      (hC₁ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    have e2 : ‖apO p.2 Q₂ g‖ ≤ max C₂ 0 * B.gN g ^ b :=
      (hC₂ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    calc _ ≤ (max C₁ 0 * B.gN g ^ a) * (max C₂ 0 * B.gN g ^ b) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (pow_nonneg hN _))
      _ = _ := by ring
  obtain ⟨C, hC⟩ := sum_bound _ (B.GV k r) (fun g => B.gN g ^ (a + b))
    (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) =>
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖) hterm
  refine ⟨C, fun g hg => ?_⟩
  have e : (fun g => Q₁ g * Q₂ g) = (fun g => Q₁ g • Q₂ g) := rfl
  rw [e, leib ops hl Q₁ h₁.1 Q₂ (smooth_ck Q₂ h₂.1) g hg]
  exact (norm_sum_map_le _ _).trans (hC g hg)

theorem apO_const : ∀ (ops : List (Bool × B.Mat k r)) (c : ℂ),
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ apO ops (fun _ : B.Mat k r => c) = fun _ => c'
  | [], c => ⟨c, le_rfl, rfl⟩
  | o :: os, c => by
    have h0 : act o (fun _ : B.Mat k r => c) = fun _ => (0 : ℂ) := by
      funext g
      rw [act_eq]
      simp
    obtain ⟨c', h1, h2⟩ := apO_const os 0
    refine ⟨c', h1.trans (by simp), ?_⟩
    simp only [apO_cons, h0, h2]

theorem good_const (c : ℂ) : Good 0 (fun _ : B.Mat k r => c) := by
  refine ⟨contDiff_const, fun ops _ => ?_⟩
  obtain ⟨c', h1, h2⟩ := apO_const ops c
  exact ⟨‖c‖, fun g _ => by rw [h2, pow_zero, mul_one]; exact h1⟩

def dirL (o : Bool × B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := dir o
      map_add' := fun a b => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.add_mul a b X
        · show -(X * (a + b)) = -(X * a) + -(X * b)
          rw [Matrix.mul_add, neg_add]
      map_smul' := fun c a => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.smul_mul c a X
        · show -(X * (c • a)) = c • -(X * a)
          rw [Matrix.mul_smul, smul_neg] }

theorem apO_clm : ∀ (ops : List (Bool × B.Mat k r)) (ℓ : B.Mat k r →L[ℝ] ℂ),
    ∃ ℓ' : B.Mat k r →L[ℝ] ℂ, apO ops ⇑ℓ = ⇑ℓ'
  | [], ℓ => ⟨ℓ, rfl⟩
  | o :: os, ℓ => by
    have h : act o ⇑ℓ = ⇑(ℓ.comp (dirL o)) := by
      funext g
      rw [act_eq]
      exact (ℓ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (curve_hasDerivAt o g) (curve_zero o g).symm).deriv
    obtain ⟨ℓ', h'⟩ := apO_clm os (ℓ.comp (dirL o))
    exact ⟨ℓ', by simp only [apO_cons, h, h']⟩

theorem sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g :=
  (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun i j => entry_le_gN g i j

theorem good_clm (ℓ : B.Mat k r →L[ℝ] ℂ) : Good 1 ⇑ℓ := by
  refine ⟨ℓ.contDiff, fun ops _ => ?_⟩
  obtain ⟨ℓ', h⟩ := apO_clm ops ℓ
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : B.Mat k r, ‖ℓ' x‖ ≤ M * ‖x‖ := by
    exact ℓ'.bound
  refine ⟨M, fun g _ => ?_⟩
  rw [h, pow_one]
  exact (hM g).trans (mul_le_mul_of_nonneg_left (sup_le_gN g) hM0.le)

def coordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def ccoordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => conj (g p.1 p.2)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp [Matrix.smul_apply, Complex.real_smul] }

def xv (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun p => g p.1 p.2) (fun p => conj (g p.1 p.2))

theorem good_var (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    Good 1 (fun g : B.Mat k r => xv g i) := by
  rcases i with p | p
  · exact good_congr (fun g => rfl) (good_clm (coordL p))
  · exact good_congr (fun g => rfl) (good_clm (ccoordL p))

theorem good_pow (Q : B.Mat k r → ℂ) (h : Good 1 Q) : ∀ m : ℕ, Good m (fun g => Q g ^ m)
  | 0 => good_congr (fun g => (pow_zero (Q g)).symm) (good_const 1)
  | m + 1 => good_congr (fun g => (pow_succ (Q g) m).symm) (good_mul _ _ (good_pow Q h m) h)

theorem good_mono_prod (d : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℕ)
    (s : Finset ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))) :
    Good (∑ i ∈ s, d i) (fun g : B.Mat k r => ∏ i ∈ s, xv g i ^ d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_const (k := k) (r := r) 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact good_congr (fun g => by rw [Finset.prod_insert ha])
      (good_mul _ _ (good_pow _ (good_var a) (d a)) ih)

theorem good_poly (q : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)
    (D : ℕ) (hq : q.totalDegree ≤ D) :
    Good D (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) := by
  have e : (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) =
      ∑ d ∈ q.support, fun g : B.Mat k r => q.coeff d * ∏ i ∈ d.support, xv g i ^ d i := by
    funext g
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ (Good D) (fun a b ha hb => good_add a b ha hb)
    (good_mono (Nat.zero_le D) _ (good_const 0)) ?_
  intro d hd
  have hdeg : (∑ i ∈ d.support, d i) ≤ D := (MvPolynomial.le_totalDegree hd).trans hq
  exact good_mono (by simpa using hdeg) _ (good_mul _ _ (good_const (q.coeff d)) (good_mono_prod d d.support))

theorem ruleC : C2.RuleC := by
  intro k r E _ _ A F D P hF hP
  obtain ⟨q, hq, hPq⟩ := hP
  exact main A D P (good_congr (fun g => (hPq g).symm) (good_poly q D hq)) F hF

end sup

end CCRuleCW
