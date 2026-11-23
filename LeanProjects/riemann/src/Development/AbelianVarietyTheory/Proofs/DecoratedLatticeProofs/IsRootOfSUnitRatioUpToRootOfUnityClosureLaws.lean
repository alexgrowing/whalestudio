import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem padicValRat_pow_mul_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a * s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.mul (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem padicValRat_pow_div_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a / s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.div (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem unitRatio_ne_zero {S : ℕ → Prop} {x y : ℂ} (h : UnitRatio S x y) : x ≠ 0 := by
  obtain ⟨hy, n, hn, r, hr, he, -⟩ := h
  intro hx
  rw [hx, zero_div, zero_pow hn.ne'] at he
  exact hr (by exact_mod_cast he.symm)

theorem unitRatio_refl (S : ℕ → Prop) {y : ℂ} (hy : y ≠ 0) : UnitRatio S y y :=
  ⟨hy, 1, one_pos, 1, one_ne_zero, by simp [div_self hy], fun p _ h => by simp at h⟩

theorem unitRatio_mul {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x * x') (y * y') := by
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨mul_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' * r' ^ n,
    mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x * x' / (y * y') = (x / y) * (x' / y') := by field_simp
    rw [this, mul_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_mul_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_div {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x / x') (y / y') := by
  have hx' := unitRatio_ne_zero h'
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨div_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' / r' ^ n,
    div_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x / x' / (y / y') = (x / y) / (x' / y') := by field_simp
    rw [this, div_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_div_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_of_pow_eq (S : ℕ → Prop) {x y : ℂ} {n : ℕ} (hy : y ≠ 0) (hn : 0 < n) (h : x ^ n = y ^ n) :
    UnitRatio S x y :=
  ⟨hy, n, hn, 1, one_ne_zero, by rw [div_pow, h, div_self (pow_ne_zero _ hy)]; simp, fun p _ h => by simp at h⟩

theorem unitRatio_prod (S : ℕ → Prop) {I : Type} (s : Finset I) (x y : I → ℂ)
    (h : ∀ i ∈ s, UnitRatio S (x i) (y i)) : UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitRatio_refl S one_ne_zero
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact unitRatio_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitRatio_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) :=
  fun S => ⟨fun y hy => unitRatio_refl S hy,
    fun x y x' y' h h' => ⟨unitRatio_mul h h', unitRatio_div h h', unitRatio_ne_zero h⟩,
    fun x y n hy hn h => unitRatio_of_pow_eq S hy hn h,
    fun I s x y h => unitRatio_prod S s x y h⟩

end GlobalTheory.Fam
