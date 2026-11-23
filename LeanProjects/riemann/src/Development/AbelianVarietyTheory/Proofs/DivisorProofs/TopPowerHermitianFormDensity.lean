import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open GlobalTheory.CxForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DensPow

variable {n : ℕ}

theorem ι_mul_ι_mul_ι_mul_ι_left (u w w' : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w') = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u)
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ w' := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w') := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem ι_mul_ι_mul_ι_mul_ι_right (u u' w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u' * ExteriorAlgebra.ι ℂ w) = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u')
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u') * ExteriorAlgebra.ι ℂ w := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u' * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w)) := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

def row (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n where
  toFun w := ∑ b, w b • sym (a, b)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem coe_row (a : Fin n) (w : Fin n → ℂ) :
    (row a w : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, w b • Pi.single (Sum.inr b) (1 : ℂ)) := by
  simp [row, sym, dzb, Finset.mul_sum, mul_smul_comm]

theorem row_mul_row (a : Fin n) (w : Fin n → ℂ) : row a w * row a w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, dz]
  exact ι_mul_ι_mul_ι_mul_ι_left _ _ _

theorem row_mul_row_of_ne {a a' : Fin n} (w : Fin n → ℂ) : row a w * row a' w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, coe_row, dz, dz]
  exact ι_mul_ι_mul_ι_mul_ι_right _ _ _

def altRows (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] Ev n where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap row
  map_eq_zero_of_eq' v i j hij hne := by
    change ∏ a, row a (v a) = 0
    rw [← Finset.mul_prod_erase Finset.univ (fun a => row a (v a)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => row a (v a))
        (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩), ← mul_assoc, hij, row_mul_row_of_ne, zero_mul]

theorem altRows_apply (v : Fin n → Fin n → ℂ) : altRows n v = ∏ a, row a (v a) := by
  first
  | rfl
  | simp only [altRows, AlternatingMap.coe_mk, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem alt_eq_det_smul {K M N : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m : ℕ} (e : Module.Basis (Fin m) K M)
    (f : M [⋀^Fin m]→ₗ[K] N) (h : Fin m → M) : f h = e.det h • f e := by
  have key : f = (LinearMap.toSpanSingleton K N (f e)).compAlternatingMap e.det := by
    refine e.ext_alternating (fun v hv => ?_)
    have hb : Function.Bijective v := Finite.injective_iff_bijective.1 hv
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective v hb
    have hσ : (fun i => e (v i)) = (⇑e) ∘ ⇑σ := rfl
    rw [hσ, LinearMap.compAlternatingMap_apply, LinearMap.toSpanSingleton_apply,
      AlternatingMap.map_perm, AlternatingMap.map_perm, e.det_self, Units.smul_def,
      Units.smul_def, smul_one_smul]
  rw [DFunLike.congr_fun key h]
  rfl

theorem prod_row (H : Matrix (Fin n) (Fin n) ℂ) : ∏ a, row a (H a) = H.det • ∏ a, sym (a, a) := by
  have h1 : ∏ a, row a (H a) = altRows n (fun a b => H a b) := (altRows_apply _).symm
  rw [h1, alt_eq_det_smul (Pi.basisFun ℂ (Fin n)), Pi.basisFun_det, altRows_apply]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [row, Pi.single_apply]

theorem add_pow_of_mul_self {R : Type*} [CommRing R] {x : R} (hx : x * x = 0) (y : R) (m : ℕ) :
    (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : R) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * y ^ m * hx

theorem sum_pow_card {R ι : Type*} [CommRing R] [DecidableEq ι] (f : ι → R) (hf : ∀ a, f a * f a = 0) (s : Finset ι) :
    (∀ m, (∑ a ∈ s, f a) ^ (s.card + 1 + m) = 0) ∧ (∑ a ∈ s, f a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun m => by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨fun m => ?_, ?_⟩
    · rw [show s.card + 1 + 1 + m = (s.card + 1 + m) + 1 by omega, add_pow_of_mul_self (hf a),
        show s.card + 1 + m + 1 = s.card + 1 + (m + 1) by omega, ih.1, ih.1]
      simp
    · rw [add_pow_of_mul_self (hf a), show s.card + 1 = s.card + 1 + 0 by rfl, ih.1, ih.2, Nat.factorial_succ]
      push_cast
      ring

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem vol_eq_smul_prod (n : ℕ) : vol n = (Complex.I / 2) ^ n • ∏ a, sym (a, a) := by
  simp only [vol, Algebra.smul_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow]

theorem dens_pow (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) :
      GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  have hω : (∑ a, ∑ b, H a b • sym (a, b) : Ev n) = ∑ a, row a (H a) := by simp [row]
  have hp : (∑ a, row a (H a)) ^ n = (n.factorial : Ev n) * ∏ a, row a (H a) := by
    simpa using (sum_pow_card (fun a => row a (H a)) (fun a => row_mul_row a _) Finset.univ).2
  have hP : (n.factorial : Ev n) * ∏ a, row a (H a) = ((n.factorial : ℂ) * H.det) • ∏ a, sym (a, a) := by
    rw [prod_row, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  rw [hω, hp, hP, Subalgebra.coe_smul, dens_smul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h1]

end GlobalTheory.CxForm.DensPow

end
