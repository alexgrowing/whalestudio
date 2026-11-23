import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Formalism.FormalDegreeBessel.FinalG
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellLieAlg

theorem mem_lieE_iff {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (P : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hP : ∀ X, X ∈ lieOf S ↔ X ∈ P) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE S ↔ unrealify x ∈ P := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      have e : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
        ext i j; rfl
      show unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ P
      rw [e]; exact (hP X).1 hX
    | zero =>
      have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.zero_mem
    | add x y _ _ hx hy =>
      have e : unrealify (x + y) = unrealify x + unrealify y := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.add_mem hx hy
    | smul c x _ hx =>
      have e : unrealify (c • x) = c • unrealify x := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.smul_mem c hx
  · intro hx
    refine Submodule.subset_span ⟨unrealify x, (hP _).2 hx, ?_⟩
    ext ⟨i, j, b⟩
    cases b <;> rfl

open scoped Matrix.Norms.Operator in
theorem mem_lieOf_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) (X : Matrix (Fin N) (Fin N) ℂ) :
    X ∈ lieOf (UH H) ↔ Xᴴ * H + H * X = 0 := by
  constructor
  · intro h
    have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) = fun _ => H := by
      funext t
      have h1 : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
      rw [← Matrix.exp_conjTranspose, Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial] at h1
      exact h1
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) _ 0 :=
      ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0).mul_const H).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
    rw [hc] at hd
    have := hd.unique (hasDerivAt_const _ _)
    simpa using this
  · intro hX t
    set Y : Matrix (Fin N) (Fin N) ℂ := (t : ℂ) • X with hYdef
    have hY : Yᴴ * H + H * Y = 0 := by
      rw [hYdef, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, ← smul_add, hX, smul_zero]
    have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hH
    have hu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hH)
    have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
      have e : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
      calc Yᴴ = Yᴴ * (H * H) := by rw [hH, Matrix.mul_one]
        _ = (Yᴴ * H) * H := by rw [Matrix.mul_assoc]
        _ = _ := by rw [e, hinv, Matrix.mul_neg]
    have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
      rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv]
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
    rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH,
      Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

open scoped Matrix.Norms.Operator in
theorem exp_mul_eq_iff {N : ℕ} (X E : Matrix (Fin N) (Fin N) ℂ) :
    (∀ t : ℝ, NormedSpace.exp (t • X) * E = E) ↔ X * E = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * E)
      (NormedSpace.exp (t • X) * X * E) t := fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).mul_const E
  constructor
  · intro h
    have h0 := hd 0
    rw [show (fun t : ℝ => NormedSpace.exp (t • X) * E) = fun _ => E from funext h] at h0
    simpa using h0.unique (hasDerivAt_const _ _)
  · intro h t
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => by rw [(hd t).deriv, Matrix.mul_assoc, h, Matrix.mul_zero]) t 0
    simpa using this

theorem mul_single_eq_iff {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    g * Matrix.single j j (1 : ℂ) = h * Matrix.single j j (1 : ℂ) ↔ g *ᵥ bvec j = h *ᵥ bvec j := by
  simp only [bvec, Matrix.mulVec_single_one]
  constructor
  · intro e
    funext i
    simpa using congrFun (congrFun e i) j
  · intro e
    ext i l
    by_cases hl : l = j
    · subst hl
      simpa using congrFun e i
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]

theorem exp_fix_iff {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) ↔ ∀ i, X i j = 0 := by
  have h1 := exp_mul_eq_iff X (Matrix.single j j (1 : ℂ))
  have h2 := mul_single_eq_iff X 0 j
  rw [Matrix.zero_mul] at h2
  rw [h2] at h1
  have h3 : X *ᵥ bvec j = (0 : Matrix (Fin N) (Fin N) ℂ) *ᵥ bvec j ↔ ∀ i, X i j = 0 := by
    simp [bvec, funext_iff]
  rw [← h3, ← h1]
  refine forall_congr' fun t => ?_
  have h4 := mul_single_eq_iff (NormedSpace.exp (t • X)) 1 j
  rw [Matrix.one_mul, Matrix.one_mulVec] at h4
  rw [h4, Complex.coe_smul]

theorem rows_zero {k r : ℕ} {X : Mat k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0)
    (hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0)
    (i : Fin (2 * r + k + 1)) (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) : X i j = 0 := by
  have hil := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hv : i'.val = 2 * r + k - i.val := rfl
  have h := congrFun (congrFun hX i') j
  have h1 : (Xᴴ * Hpk k r) i' j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.conjTranspose_apply, hc i' (by omega) l, star_zero, zero_mul]
  have h2 : (Hpk k r * X) i' j = X i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · have : Hpk k r i' i = 1 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, one_mul]
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun e => hl (Fin.ext e)
      have : Hpk k r i' l = 0 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · simp
  rw [Matrix.add_apply, h1, h2, zero_add] at h
  exact h

theorem mem_lieOf_UWb (k r : ℕ) (X : Mat k r) :
    X ∈ lieOf (Formalism.FourierDecayAlt.B2.UWb k r) ↔ (Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0) := by
  have hH := (hpkFacts k r).2.1
  constructor
  · intro h
    have hX := (mem_lieOf_UH _ hH X).1 fun t => (h t).1
    have hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0 := by
      intro j hj
      have hjl := j.isLt
      by_cases hr : j.val < r
      · exact (exp_fix_iff X j).1 fun t => ((h t).2 ⟨j.val, hr⟩).1
      · have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rw [← e]
        exact (exp_fix_iff X _).1 fun t => ((h t).2 _).2
    refine ⟨hX, fun i j hij => ?_⟩
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · exact hc j (fun hj => hij ⟨hi, hj⟩) i
    · exact rows_zero hX hc i hi j
  · rintro ⟨hX, h0⟩ t
    refine ⟨(mem_lieOf_UH _ hH X).2 hX t, fun a => ⟨?_, ?_⟩⟩
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.1; have := a.isLt
      simp only [eI] at *; omega
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.2; have := a.isLt
      simp only [esI] at *; omega

def skewSub {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    have ha' : aᴴ * H + H * a = 0 := ha
    have hb' : bᴴ * H + H * b = 0 := hb
    show (a + b)ᴴ * H + H * (a + b) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' c a ha := by
    have ha' : aᴴ * H + H * a = 0 := ha
    show (c • a)ᴴ * H + H * (c • a) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha', smul_zero]

def midSub (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {a b} ha hb := fun i j h => by rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  smul_mem' c a ha := fun i j h => by rw [Matrix.smul_apply, ha i j h, smul_zero]

theorem lie_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  intro k r x
  have h2 := mem_lieE_iff (S := Formalism.FourierDecayAlt.B2.UWb k r) (skewSub (Hpk k r) ⊓ midSub k r) (mem_lieOf_UWb k r) x
  refine ⟨mem_lieE_iff (skewSub (Hpk k r)) (mem_lieOf_UH _ (hpkFacts k r).2.1) x, h2, fun hx => ?_⟩
  have h := (mem_lieOf_UWb k r _).2 (h2.1 hx) 1
  simpa using h

end GlobalTheory.CellLieAlg
