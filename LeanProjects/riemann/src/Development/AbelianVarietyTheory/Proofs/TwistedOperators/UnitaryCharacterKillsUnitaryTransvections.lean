import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
open scoped Matrix

namespace GlobalTheory.UTrans.TvKill

open GlobalTheory.UTrans GlobalTheory.UTrans.Calc

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

def rk (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun a b => x a * ∑ e, G b e * σ (y e)

theorem rk_mulVec (x y v : Fin n → E) : rk σ G x y *ᵥ v = hf σ G v y • x := by
  funext a
  simp only [rk, Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem exists_dual (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0) : ∃ y, hf σ G x y = 1 := by
  have h1 : Matrix.vecMul x G ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hG.det_ne h)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h1
  refine ⟨Pi.single b (σ (Matrix.vecMul x G b)⁻¹), ?_⟩
  have : hf σ G x (Pi.single b (σ (Matrix.vecMul x G b)⁻¹)) =
      Matrix.vecMul x G b * (Matrix.vecMul x G b)⁻¹ := by
    simp only [hf, Pi.single_apply, apply_ite σ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hG.invol, ← Finset.sum_mul]
    rfl
  rw [this, mul_inv_cancel₀ hb]

theorem exists_dual_iso [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ y, hf σ G x y = 1 ∧ hf σ G y y = 0 := by
  obtain ⟨y, hy⟩ := exists_dual hG hx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(hf σ G y y / 2)) = -(hf σ G y y / 2) := by
    rw [map_neg, map_div₀, hf_conj σ G hG.invol hG.herm, map_ofNat]
  refine ⟨y + (-(hf σ G y y / 2)) • x, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hxx, hy]; ring
  · simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx]
    ring

theorem exists_double [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ γ, IsU σ G γ ∧ γ *ᵥ x = (2 : E) • x := by
  obtain ⟨y, hy, hyy⟩ := exists_dual_iso hG hx hxx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(1 / 2)) = -(1 / 2) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  have hm : ∀ v, (1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x) *ᵥ v =
      v + hf σ G v y • x + (-(1 / 2) : E) • hf σ G v x • y := by
    intro v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
      rk_mulVec]
  refine ⟨1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x, ?_, ?_⟩
  · intro v w
    rw [hm, hm]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx, hyy,
      hf_conj σ G hG.invol hG.herm]
    ring
  · rw [hm, hy, hxx, zero_smul, smul_zero, add_zero, one_smul, two_smul]

theorem char_tvGen : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  intro E _ _ n σ G hG A _ X hX
  have hU1 : IsU σ G 1 := fun x y => by simp
  have hX1 : X 1 = 1 := by
    have := hX 1 1 hU1 hU1
    rw [mul_one] at this
    exact mul_eq_left.mp this.symm
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ X m = 1 := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      have hUq : ∀ q : ℚ, IsU σ G (tv σ G x (q * t)) := by
        intro q
        refine isU_tv σ G hG.invol hG.herm x _ ?_
        rw [hx, map_mul, map_ratCast]
        linear_combination (q : E) * ht
      have hUt : IsU σ G (tv σ G x t) := by simpa using hUq 1
      refine ⟨hUt, ?_⟩
      by_cases hx0 : x = 0
      · subst hx0
        have : tv σ G 0 t = 1 := by
          ext a b
          simp [tv]
        rw [this, hX1]
      · obtain ⟨γ, hγ, hγx⟩ := exists_double hG hx0 hx
        have h3 : IsU σ G (tv σ G x (1 / 3 * t)) := by
          have := hUq (1 / 3)
          push_cast at this
          exact this
        have hc := conj_tv σ G γ x (1 / 3 * t) hγ
        have he : tv σ G (γ *ᵥ x) (1 / 3 * t) = tv σ G x (1 / 3 * t) * tv σ G x t := by
          rw [hγx, tv_smul, tv_mul, hx, map_ofNat]
          congr 1
          ring
        rw [he] at hc
        have h4 := congrArg X hc
        rw [hX _ _ hγ h3, hX _ _ (isU_mul σ G _ _ h3 hUt) hγ, hX _ _ h3 hUt, mul_comm (X γ)] at h4
        exact mul_eq_left.mp (mul_right_cancel h4).symm
    | one => exact ⟨hU1, hX1⟩
    | mul a b _ _ ha hb =>
      exact ⟨isU_mul σ G _ _ ha.1 hb.1, by rw [hX _ _ ha.1 hb.1, ha.2, hb.2, mul_one]⟩
  exact fun m hm => (key m hm).2

end GlobalTheory.UTrans.TvKill
