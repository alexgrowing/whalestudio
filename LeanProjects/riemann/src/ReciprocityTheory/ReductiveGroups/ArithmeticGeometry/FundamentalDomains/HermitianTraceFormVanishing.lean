import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Lemmata.GeneralBFactAltForm.Imports

namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[simp] lemma cc_cc (a : E) : cc (cc a) = a := by simp [cc]
@[simp] lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by simp [cc]
@[simp] lemma cc_add (a b : E) : cc (a + b) = cc a + cc b := by simp [cc]
@[simp] lemma cc_sub (a b : E) : cc (a - b) = cc a - cc b := by simp [cc]
@[simp] lemma cc_neg (a : E) : cc (-a) = -cc a := by simp [cc]
@[simp] lemma cc_zero : cc (0 : E) = 0 := by simp [cc]
@[simp] lemma cc_one : cc (1 : E) = 1 := by simp [cc]
@[simp] lemma cc_inv (a : E) : cc a⁻¹ = (cc a)⁻¹ := by simp [cc]
lemma cc_sum {ι : Type*} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]
@[simp] lemma cc_eq_zero (a : E) : cc a = 0 ↔ a = 0 := by simp [cc]
@[simp] lemma cc_intCast (n : ℤ) : cc (n : E) = n := by simp [cc]
@[simp] lemma cc_natCast (n : ℕ) : cc (n : E) = n := by simp [cc]

variable {r : ℕ}

lemma herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

lemma herm_sub_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x - x') y = herm G x y - herm G x' y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_sub_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y - y') = herm G x y - herm G x y' := by
  simp [herm, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma herm_conj (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma cc_single (b c : Fin r) :
    cc ((Pi.single b (1 : E) : Fin r → E) c) = (Pi.single b (1 : E) : Fin r → E) c := by
  by_cases h : c = b
  · subst h; simp
  · simp [h]

lemma herm_single_right (G : Matrix (Fin r) (Fin r) E) (v : Fin r → E) (b : Fin r) :
    herm G v (Pi.single b 1) = (Matrix.vecMul v G) b := by
  simp only [herm, cc_single, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Pi.single_apply]

lemma eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (v : Fin r → E)
    (hv : ∀ y, herm G v y = 0) : v = 0 := by
  apply Matrix.eq_zero_of_vecMul_eq_zero hG
  funext b
  rw [← herm_single_right]
  simpa using hv _

lemma exists_eq_smul_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hGh : ∀ a b, cc (G a b) = G b a) (ξ μ : Fin r → E) (hξ : ξ ≠ 0)
    (h : ∀ y, herm G y ξ = 0 → herm G μ y = 0) : ∃ e : E, μ = e • ξ := by
  have hk : ∃ k, herm G (Pi.single k 1) ξ ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    apply hξ
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    rw [← herm_single_right, ← herm_conj G hGh, hne b]
    simp
  obtain ⟨k, hk⟩ := hk
  set y0 : Fin r → E := (herm G (Pi.single k 1) ξ)⁻¹ • Pi.single k 1
  have hy0 : herm G y0 ξ = 1 := by
    simp only [y0, herm_smul_left]; exact inv_mul_cancel₀ hk
  refine ⟨herm G μ y0, ?_⟩
  have hall : ∀ y, herm G (μ - herm G μ y0 • ξ) y = 0 := by
    intro y
    have h1 := h (y - herm G y ξ • y0) (by rw [herm_sub_left, herm_smul_left, hy0]; ring)
    rw [herm_sub_right, herm_smul_right, herm_conj G hGh, sub_eq_zero] at h1
    rw [herm_sub_left, herm_smul_left, h1]
    ring
  have := eq_zero_of_herm G hG _ hall
  exact sub_eq_zero.mp this

lemma eq_zero_of_trace (a : E) (h : ∀ β : 𝓞 E, Algebra.trace ℚ E (cc (β : E) * a) = 0) :
    a = 0 := by
  by_contra ha
  have halg : IsAlgebraic ℤ (cc a⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  let β : 𝓞 E := ⟨y • cc a⁻¹, hint⟩
  have hβ : (β : E) = y • cc a⁻¹ := rfl
  have h1 := h β
  have h2 : cc (y • cc a⁻¹) * a = algebraMap ℚ E (y : ℚ) := by
    rw [zsmul_eq_mul, cc_mul, cc_intCast, cc_cc, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    simp
  rw [hβ, h2, Algebra.trace_algebraMap] at h1
  have hd : (Module.finrank ℚ E : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  rw [nsmul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact hd h3
  · exact hy (by exact_mod_cast h3)

theorem exists_smul_mem {R F X : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.general_b_fact_alt_form.goal1 S hx

end ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
