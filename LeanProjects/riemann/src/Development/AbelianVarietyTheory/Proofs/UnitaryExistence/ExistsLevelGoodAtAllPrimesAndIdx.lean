import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelAllPrimes

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    ((c : 𝓞 E) + H.rt) * (c - H.rt) = ((c ^ 2 + H.d : ℕ) : 𝓞 E) := by
  push_cast
  linear_combination (-1 : 𝓞 E) * H.rt_sq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {c : ℕ} (hc : Nat.Coprime c H.d)
    (ho : Odd (c ^ 2 + H.d)) :
    IsCoprime ((c : 𝓞 E) + H.rt) (c - H.rt) := by
  have h2 : Nat.Coprime 2 (c ^ 2 + H.d) := (Nat.coprime_two_left).2 ho
  have hc' : Nat.Coprime c (c ^ 2 + H.d) := by
    rw [sq, add_comm]
    exact (Nat.coprime_add_mul_right_right c H.d c).2 hc
  have hcop : IsCoprime ((2 * c : ℕ) : ℤ) ((c ^ 2 + H.d : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul h2 hc')
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (Int.cast : ℤ → 𝓞 E) huv
  push_cast at key
  refine ⟨(u : 𝓞 E) + v * (c - H.rt), u, ?_⟩
  linear_combination key - (v : 𝓞 E) * H.rt_sq

end GlobalTheory.LevelAllPrimes

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem host_bar_rt' (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : starRingEnd ℂ (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz : z ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa [z] using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
    have hx : z.re = 0 := by
      rcases mul_eq_zero.1 (by linarith : z.re * z.im = 0) with h | h
      · exact h
      · rw [h] at hre; nlinarith
    apply Complex.ext <;> simp [hx]
  have key : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
    rw [H.bar_eq]
    apply φ.injective
    simpa [IsCMField.complexEmbedding_complexConj] using hconj
  exact RingOfIntegers.coe_injective key

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem natCast_add_rt_mem_adjoin_w0 (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    (c : 𝓞 E) + H.rt ∈ Algebra.adjoin ℤ {H.w0} := by
  rw [show (c : 𝓞 E) + H.rt = ((c : 𝓞 E) - 1) + 2 * H.w0 by linear_combination -H.two_weight_eq_one_add_root]
  have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ H.w0
  have h2 : (2 : 𝓞 E) ∈ Algebra.adjoin ℤ {H.w0} := by
    simpa using natCast_mem (Algebra.adjoin ℤ {H.w0}) 2
  exact add_mem (sub_mem (natCast_mem _ c) (one_mem _)) (mul_mem h2 hw)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem three_le_mul_div_prime_pow_factorization {a b : ℕ} (p : ℕ) (hab : Nat.Coprime a b)
    (ha : 3 ≤ a) (hb : 3 ≤ b) : 3 ≤ a * b / p ^ (a * b).factorization p := by
  have key : ∀ {x y : ℕ}, 3 ≤ x → 0 < y → x.factorization p = 0 →
      3 ≤ x * y / p ^ (x * y).factorization p := by
    intro x y hx hy hxp
    rw [Nat.factorization_mul (by omega) hy.ne', Finsupp.add_apply, hxp, zero_add,
      Nat.mul_div_assoc x (Nat.ordProj_dvd y p)]
    have : 1 ≤ y / p ^ y.factorization p :=
      Nat.div_pos (Nat.le_of_dvd hy (Nat.ordProj_dvd y p)) (Nat.ordProj_pos y p)
    nlinarith
  by_cases hap : a.factorization p = 0
  · exact key ha (by omega) hap
  · have hbp : b.factorization p = 0 := by
      by_contra hbp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.2 hap)
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos hap
      have hpb : p ∣ b := Nat.dvd_of_factorization_pos hbp
      have hg := Nat.dvd_gcd hpa hpb
      rw [hab.gcd_eq_one] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.1 hg)
    rw [mul_comm]
    exact key hb (by omega) hbp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.exists_level_goodAt_all_primes_and_idx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (A : ℕ), 0 < A →
      ∃ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.A = A ∧ (∀ p : ℕ, p.Prime → l.GoodAt p) ∧
        ∀ p : ℕ, p.Prime → ∃ i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Idx H p, i.l = l := by
  intro E _ _ _ H A hA
  obtain ⟨k, hk⟩ : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  have h2d : Nat.Coprime 2 H.d := (Nat.coprime_two_left).2 ⟨k, hk⟩
  have h4d : Nat.Coprime (2 ^ 2 + H.d) H.d := by
    rw [Nat.coprime_add_self_left]
    exact Nat.Coprime.pow_left 2 h2d
  have hc1 : Nat.Coprime 2 H.d := h2d
  have hc2 : Nat.Coprime (2 * (2 ^ 2 + H.d)) H.d := Nat.Coprime.mul h2d h4d
  have ho1 : Odd (2 ^ 2 + H.d) := ⟨2 + k, by rw [hk]; ring⟩
  have ho2 : Odd ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    refine Even.add_odd ?_ ⟨k, hk⟩
    rw [sq]
    exact (even_two_mul _).mul_right _
  have hM : Nat.Coprime (2 ^ 2 + H.d) ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    rw [show (2 * (2 ^ 2 + H.d)) ^ 2 + H.d = H.d + (4 * (2 ^ 2 + H.d)) * (2 ^ 2 + H.d) by ring,
      Nat.coprime_add_mul_right_right]
    exact h4d
  have e1 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H 2
  have e2 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H (2 * (2 ^ 2 + H.d))
  set M₁ := 2 ^ 2 + H.d with hM₁
  set c := 2 * M₁ with hc
  set M₂ := c ^ 2 + H.d with hM₂
  have hMcop : IsCoprime (M₁ : 𝓞 E) (M₂ : 𝓞 E) := by
    have := (Nat.isCoprime_iff_coprime.2 hM).map (Int.castRingHom (𝓞 E))
    simpa using this
  set al := ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) with hal
  have hbar : H.bar al = ((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt) := by
    simp only [hal, map_mul, map_add, map_natCast, host_bar_rt', sub_eq_add_neg]
  have hmem : al ∈ Algebra.adjoin ℤ {H.w0} :=
    mul_mem (natCast_add_rt_mem_adjoin_w0 H 2) (natCast_add_rt_mem_adjoin_w0 H c)
  have hprod : al * H.bar al = ((M₁ * M₂ : ℕ) : 𝓞 E) := by
    rw [hbar, hal, show ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) * (((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt))
      = (((2 : ℕ) + H.rt) * ((2 : ℕ) - H.rt)) * (((c : 𝓞 E) + H.rt) * ((c : 𝓞 E) - H.rt)) by ring,
      e1, e2]
    exact (Nat.cast_mul _ _).symm
  have hcop : IsCoprime al (H.bar al) := by
    rw [hbar, hal]
    refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc1 ho1
    · exact (hMcop.of_isCoprime_of_dvd_left (Dvd.intro _ e1)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e2)
    · exact (hMcop.symm.of_isCoprime_of_dvd_left (Dvd.intro _ e2)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e1)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc2 ho2
  have h3₁ : 3 ≤ M₁ := by omega
  have h3₂ : 3 ≤ M₂ := by have := Nat.zero_le (c ^ 2); have := H.d_prime.two_le; omega
  obtain ⟨l, hlM, hlA, -⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).1 E H al (M₁ * M₂) A
    hmem hprod hcop (le_trans h3₁ (Nat.le_mul_of_pos_right _ (by omega)))
    (Nat.odd_mul.2 ⟨ho1, ho2⟩) hA
  have hgood : ∀ p : ℕ, p.Prime → l.GoodAt p := by
    intro p _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    rw [hlM]
    exact three_le_mul_div_prime_pow_factorization p hM h3₁ h3₂
  refine ⟨l, hlA, hgood, fun p hp => ?_⟩
  obtain ⟨cf⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).2.2 E H l
  exact ⟨{ l := l, c := cf, good := hgood p hp }, rfl⟩

end GlobalTheory
