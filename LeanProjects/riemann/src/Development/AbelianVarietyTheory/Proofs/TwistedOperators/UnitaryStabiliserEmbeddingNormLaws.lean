import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal

variable {n : ℕ}

section Entries

variable (e : Option (Fin n) ≃ Fin (n + 1))

@[simp] theorem embH_ss (h : Mat n) (i j : Fin n) : embH e h (e (some i)) (e (some j)) = h i j := by
  simp only [embH, Equiv.symm_apply_apply]
@[simp] theorem embH_nn (h : Mat n) : embH e h (e none) (e none) = 1 := by
  simp only [embH, Equiv.symm_apply_apply]
@[simp] theorem embH_ns (h : Mat n) (j : Fin n) : embH e h (e none) (e (some j)) = 0 := by
  simp only [embH, Equiv.symm_apply_apply]
@[simp] theorem embH_sn (h : Mat n) (i : Fin n) : embH e h (e (some i)) (e none) = 0 := by
  simp only [embH, Equiv.symm_apply_apply]
@[simp] theorem embL_ss (h : Mat n) (i j : Fin n) : embL e h (e (some i)) (e (some j)) = h i j := by
  simp only [embL, Equiv.symm_apply_apply]
@[simp] theorem embL_nn (h : Mat n) : embL e h (e none) (e none) = 0 := by
  simp only [embL, Equiv.symm_apply_apply]
@[simp] theorem embL_ns (h : Mat n) (j : Fin n) : embL e h (e none) (e (some j)) = 0 := by
  simp only [embL, Equiv.symm_apply_apply]
@[simp] theorem embL_sn (h : Mat n) (i : Fin n) : embL e h (e (some i)) (e none) = 0 := by
  simp only [embL, Equiv.symm_apply_apply]

theorem sum_e {M : Type} [AddCommMonoid M] (f : Fin (n + 1) → M) : ∑ a, f a = f (e none) + ∑ i, f (e (some i)) := by
  rw [← e.sum_comp, Fintype.sum_option]

theorem ext_e {A B : Mat (n + 1)} (h : ∀ x y, A (e x) (e y) = B (e x) (e y)) : A = B := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  exact h a b

theorem embH_eq (h : Mat n) : embH e h = embL e h + embH e 0 := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp

theorem embL_mul (a b : Mat n) : embL e (a * b) = embL e a * embL e b := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp [Matrix.mul_apply, sum_e e]

theorem embL_mul_q (a : Mat n) : embL e a * embH e 0 = 0 := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp [Matrix.mul_apply, sum_e e]

theorem q_mul_embL (a : Mat n) : embH e 0 * embL e a = 0 := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp [Matrix.mul_apply, sum_e e]

theorem embH_conj (h : Mat n) : (embH e h)ᴴ = embH e hᴴ := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp [Matrix.conjTranspose_apply]

theorem embL_conj (h : Mat n) : (embL e h)ᴴ = embL e hᴴ := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp [Matrix.conjTranspose_apply]

theorem embH_inj : Function.Injective (embH e) := by
  intro a b h
  ext i j
  rw [← embH_ss e a, h, embH_ss]

def embLₗ : Mat n →ₗ[ℂ] Mat (n + 1) where
  toFun := embL e
  map_add' a b := by
    refine ext_e e fun x y => ?_
    cases x <;> cases y <;> simp
  map_smul' c a := by
    refine ext_e e fun x y => ?_
    cases x <;> cases y <;> simp

theorem embL_smul (t : ℝ) (X : Mat n) : embL e (t • X) = t • embL e X := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp

theorem embH_jm {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} (hs : Signs e ε ε') : Jm ε = embH e (Jm ε') := by
  refine ext_e e fun x y => ?_
  cases x <;> cases y <;> simp [Jm, Matrix.diagonal_apply, hs.1, hs.2]

end Entries

section Group

theorem jm_mul_jm {m : ℕ} (ε : Fin m → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

theorem inv_of_mem {m : ℕ} {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : g⁻¹ = Jm ε * gᴴ * Jm ε := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, jm_mul_jm]

theorem inv_mul_of_mem {m : ℕ} {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : g⁻¹ * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [inv_of_mem hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, jm_mul_jm]

variable (e : Option (Fin n) ≃ Fin (n + 1)) {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

theorem embH_mem (hs : Signs e ε ε') {h : Mat n} (hh : h ∈ UJset ε') : embH e h ∈ UJset ε := by
  have h1 : hᴴ * Jm ε' * h = Jm ε' := hh
  show (embH e h)ᴴ * Jm ε * embH e h = Jm ε
  rw [embH_jm e hs, embH_conj, ← embH_mul, ← embH_mul, h1]

theorem embH_inv (hh : ∀ h ∈ UJset ε', embH e h ∈ UJset ε) {h : Mat n} (hm : h ∈ UJset ε') : (embH e h)⁻¹ = embH e h⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← embH_mul, inv_mul_of_mem hm, embH_one]

theorem colLen_mul (g : Mat (n + 1)) (h : Mat n) : colLen e (g * embH e h) = colLen e g := by
  unfold colLen
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  rw [Matrix.mul_apply, sum_e e]
  simp

theorem embL_lie (hs : Signs e ε ε') {X : Mat n} (hX : X ∈ lieOf (Jm ε')) : embL e X ∈ lieOf (Jm ε) := by
  have h1 : Xᴴ * Jm ε' + Jm ε' * X = 0 := hX
  show (embL e X)ᴴ * Jm ε + Jm ε * embL e X = 0
  rw [embH_jm e hs, embL_conj, embH_eq e (Jm ε'), Matrix.mul_add, Matrix.add_mul, ← embL_mul, ← embL_mul, embL_mul_q,
    q_mul_embL, add_zero, add_zero]
  have h2 := (embLₗ e).map_add (Xᴴ * Jm ε') (Jm ε' * X)
  simp only [embLₗ, LinearMap.coe_mk, AddHom.coe_mk] at h2
  rw [← h2, h1]
  exact (embLₗ e).map_zero

theorem stab (hs : Signs e ε ε') {g : Mat (n + 1)} (hg : g ∈ UJset ε) (hc : ∀ a, g a (e none) = if a = e none then 1 else 0) :
    ∃ h ∈ UJset ε', g = embH e h := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  have hr : ∀ b, g (e none) b = if b = e none then 1 else 0 := by
    intro b
    have h1 := congrFun (congrFun hJ b) (e none)
    simp only [Matrix.mul_apply, hc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hs.1, mul_one] at h1
    have h2 := congrArg star h1
    simp only [star_star] at h2
    rw [h2]
    by_cases hb : b = e none
    · subst hb; simp [hs.1]
    · simp [hb]
  let h : Mat n := fun i j => g (e (some i)) (e (some j))
  have hgh : g = embH e h := by
    refine ext_e e fun x y => ?_
    cases x <;> cases y
    · simp [hc]
    · simp [hr]
    · simp [hc]
    · exact (embH_ss e h _ _).symm
  refine ⟨h, ?_, hgh⟩
  apply embH_inj e
  show embH e (hᴴ * Jm ε' * h) = embH e (Jm ε')
  rw [embH_mul, embH_mul, ← embH_conj, ← hgh, ← embH_jm e hs, hJ]

end Group

section Norms

theorem hsn_sq {m : ℕ} (g : Mat m) : hsn g ^ 2 = ∑ a, ∑ b, ‖g a b‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

variable (e : Option (Fin n) ≃ Fin (n + 1))

theorem hsn_embH (h : Mat n) : hsn (embH e h) ^ 2 = hsn h ^ 2 + 1 := by
  rw [hsn_sq, hsn_sq, sum_e e]
  simp [sum_e e]
  ring

theorem hsn_embL (X : Mat n) : hsn (embL e X) = hsn X := by
  unfold hsn
  congr 1
  simp [sum_e e]

theorem colLen_le (g : Mat (n + 1)) : colLen e g ≤ hsn g := by
  unfold colLen hsn
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun a _ => ?_
  exact Finset.single_le_sum (f := fun b => ‖g a b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ _)

theorem one_le_colLen {ε : Fin (n + 1) → Bool} (h0 : ε (e none) = true) {g : Mat (n + 1)} (hg : g ∈ UJset ε) : 1 ≤ colLen e g := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  have h1 := congrFun (congrFun hJ (e none)) (e none)
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, if_true, h0] at h1
  have h2 : ∀ c, star (g c (e none)) * (if ε c = true then 1 else -1) * g c (e none) =
      (((if ε c = true then 1 else -1 : ℝ) * ‖g c (e none)‖ ^ 2 : ℝ) : ℂ) := by
    intro c
    rw [mul_comm (star _), mul_assoc, Complex.star_def, Complex.conj_mul']
    split_ifs <;> push_cast <;> ring
  simp only [h2] at h1
  rw [← Complex.ofReal_sum] at h1
  have h3 : ∑ c, (if ε c = true then 1 else -1 : ℝ) * ‖g c (e none)‖ ^ 2 = 1 := by exact_mod_cast h1
  have h4 : 1 ≤ ∑ a, ‖g a (e none)‖ ^ 2 := by
    rw [← h3]
    refine Finset.sum_le_sum fun c _ => ?_
    split_ifs
    · simp
    · nlinarith [sq_nonneg ‖g c (e none)‖]
  unfold colLen
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt h4

theorem hsn_inv {m : ℕ} {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : hsn g⁻¹ = hsn g := by
  rw [inv_of_mem hg]
  unfold hsn
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem hsn_eq_norm {m : ℕ} (g : Mat m) :
    hsn g = @Norm.norm (Mat m) Matrix.frobeniusSeminormedAddCommGroup.toNorm g := by
  rw [@Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  norm_cast

theorem hsn_mul {m : ℕ} (g g' : Mat m) : hsn (g * g') ≤ hsn g * hsn g' := by
  rw [hsn_eq_norm, hsn_eq_norm, hsn_eq_norm]
  exact @Matrix.frobenius_norm_mul _ _ _ _ _ _ _ _ g g'

theorem embH_cont : Continuous (embH e) := by
  have h : embH e = fun h => embLₗ e h + embH e 0 := funext fun h => embH_eq e h
  rw [h]
  exact (LinearMap.continuous_of_finiteDimensional _).add continuous_const

def blkH : Mat n × ℂ →+* Mat (n + 1) where
  toFun p := embL e p.1 + p.2 • embH e 0
  map_one' := by
    show embL e 1 + (1 : ℂ) • embH e 0 = 1
    rw [one_smul, ← embH_eq, embH_one]
  map_mul' p q := by
    show embL e (p.1 * q.1) + (p.2 * q.2) • embH e 0 = (embL e p.1 + p.2 • embH e 0) * (embL e q.1 + q.2 • embH e 0)
    have qq : embH e 0 * embH e 0 = embH e 0 := by rw [← embH_mul, mul_zero]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, embL_mul, embL_mul_q, q_mul_embL, qq,
      smul_zero, add_zero, zero_add, smul_smul, mul_comm]
  map_zero' := by
    show embL e 0 + (0 : ℂ) • embH e 0 = 0
    rw [zero_smul, add_zero]
    exact (embLₗ e).map_zero
  map_add' p q := by
    show embL e (p.1 + q.1) + (p.2 + q.2) • embH e 0 = (embL e p.1 + p.2 • embH e 0) + (embL e q.1 + q.2 • embH e 0)
    rw [show embL e (p.1 + q.1) = embL e p.1 + embL e q.1 from (embLₗ e).map_add _ _, add_smul]
    abel

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exp_embL (X : Mat n) : NormedSpace.exp (embL e X) = embH e (NormedSpace.exp X) := by
  have hc : Continuous (blkH e) := by
    show Continuous fun p : Mat n × ℂ => embLₗ e p.1 + p.2 • embH e 0
    exact ((LinearMap.continuous_of_finiteDimensional _).comp continuous_fst).add (continuous_snd.smul continuous_const)
  have h := NormedSpace.map_exp (blkH e) hc (X, 0)
  have h1 : blkH e (X, 0) = embL e X := by
    show embL e X + (0 : ℂ) • embH e 0 = _
    simp
  rw [h1] at h
  refine h.symm.trans ?_
  show embL e (NormedSpace.exp (X, (0 : ℂ))).1 + (NormedSpace.exp (X, (0 : ℂ))).2 • embH e 0 = _
  have e1 : (NormedSpace.exp (X, (0 : ℂ))).1 = NormedSpace.exp X := Prod.fst_exp (X, (0 : ℂ))
  have e2 : (NormedSpace.exp (X, (0 : ℂ))).2 = NormedSpace.exp 0 := Prod.snd_exp (X, (0 : ℂ))
  rw [e1, e2, NormedSpace.exp_zero, one_smul, ← embH_eq]

end Norms

theorem embLaws : EmbLaws := by
  intro n e ε ε' hs
  have hmem : ∀ h ∈ UJset ε', embH e h ∈ UJset ε := fun h hh => embH_mem e hs hh
  refine ⟨hmem, embH_mul e, embH_cont e, fun h hh => embH_inv e hmem hh, colLen_mul e, fun g hg hc => stab e hs hg hc,
    fun X hX => embL_lie e hs hX, fun t X => ?_, hsn_embH e, hsn_embL e, colLen_le e,
    fun g hg => ⟨one_le_colLen e hs.1 hg, hsn_inv hg⟩, hsn_mul⟩
  rw [← embL_smul, exp_embL]

end GlobalTheory.SepReal
