import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem norm_eq_one_of_pow_eq_one' {R : Type} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n)
    (h : z ^ n = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 h1

theorem dirichlet_pow_card_eq_one {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (l : ℕ) (h : l.Coprime M) :
    ∃ n : ℕ, 0 < n ∧ χ (l : ZMod M) ^ n = 1 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, ?_⟩
  rw [← ZMod.coe_unitOfCoprime l h, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one,
    map_one]

theorem hecke_gap (L : ℝ) (hL : 3 ≤ L) (e : ℕ) (he : 1 ≤ e) :
    L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) + L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) < L ^ (2 * e) - 1 := by
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg L
  have hss : s * s = L := Real.mul_self_sqrt hL0.le
  have h1 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2) = L ^ e * s := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast L e, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  have h2 : L ^ (((2 * e + 1 : ℕ) : ℝ) / 2 - 1) = L ^ e * s / L := by
    rw [Real.rpow_sub hL0, Real.rpow_one, h1]
  rw [h1, h2]
  set N := L ^ e with hN
  have hNL : L ≤ N := by
    rw [hN]; calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ e := pow_le_pow_right₀ (by linarith) he
  have hsL : s < L - 1 := by nlinarith
  have key : N * s * (L + 1) < L * (N ^ 2 - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hNL) (show 0 ≤ L * (N + L) - (L + 1) * s by nlinarith),
      mul_pos (mul_pos (show (0:ℝ) < L + 1 by linarith) hL0) (show 0 < L - 1 - s by linarith)]
  have : N * s + N * s / L = N * s * (L + 1) / L := by field_simp
  rw [this, div_lt_iff₀ hL0]
  have : L ^ (2 * e) = N ^ 2 := by rw [hN, ← pow_mul, mul_comm]
  rw [this]; linarith

theorem heckePoly_root_eq {k : ℕ} (g : Newform k) (p : ℕ) (α : ℂ) (h : (g.heckePoly p).IsRoot α) :
    g.a p * α = α ^ 2 + g.χ (p : ZMod g.M) * (p : ℂ) ^ (k - 1) := by
  have := h.eq_zero
  simp only [Newform.heckePoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at this
  linear_combination -this

theorem root_facts_of_bound
    (hbd : ∀ (k : ℕ) (g : Newform k) (p : ℕ), p.Prime → ¬ p ∣ g.M →
      ‖g.a p‖ ≤ (p : ℝ) ^ ((k : ℝ) / 2) + (p : ℝ) ^ ((k : ℝ) / 2 - 1)) :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  intro l _ ι e g α hl2 he hdiv hroot hα
  have hp : l.Prime := Fact.out
  have hcop : l.Coprime g.M := (Nat.Prime.coprime_iff_not_dvd hp).2 hdiv
  obtain ⟨n, hn, hχn⟩ := dirichlet_pow_card_eq_one g.pos g.χ l hcop
  have hrel := heckePoly_root_eq g l α hroot
  have hk : 2 * e + 1 - 1 = 2 * e := by omega
  rw [hk] at hrel
  set c := g.χ (l : ZMod g.M) with hc
  have hα0 : α ≠ 0 := by
    rintro rfl; simp at hα
  refine ⟨?_, ?_⟩
  ·
    have hA0 : ι.symm α ≠ 0 := by rw [Ne, map_eq_zero_iff _ ι.symm.injective]; exact hα0
    have hrel' : ι.symm (g.a l) = ι.symm α + ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α := by
      field_simp
      have := congrArg ι.symm hrel
      simp only [map_mul, map_add, map_pow, map_natCast] at this
      linear_combination this
    have hcn : ‖ι.symm c‖ = 1 :=
      norm_eq_one_of_pow_eq_one' hn (by rw [← map_pow, hχn, map_one])
    have hln : ‖(l : Qbar l)‖ < 1 := by
      have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
      rw [h, PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
    have hB : ‖ι.symm c * (l : Qbar l) ^ (2 * e) / ι.symm α‖ < 1 := by
      rw [norm_div, norm_mul, norm_pow, hcn, hα, one_mul, div_one]
      exact pow_lt_one₀ (norm_nonneg _) hln (by omega)
    rw [hrel', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hα]; exact hB.ne'), hα]
    exact max_eq_left hB.le
  ·
    intro m hm hαm
    have hαn : ‖α‖ = 1 := norm_eq_one_of_pow_eq_one' hm hαm
    have hcn : ‖c‖ = 1 := norm_eq_one_of_pow_eq_one' hn hχn
    have hb := hbd (2 * e + 1) g l hp hdiv
    have ha : g.a l = α + c * (l : ℂ) ^ (2 * e) / α := by
      field_simp; linear_combination hrel
    have hlow : (l : ℝ) ^ (2 * e) - 1 ≤ ‖g.a l‖ := by
      have h1 : ‖c * (l : ℂ) ^ (2 * e) / α‖ = (l : ℝ) ^ (2 * e) := by
        rw [norm_div, norm_mul, norm_pow, hcn, hαn, one_mul, div_one, Complex.norm_natCast]
      have h2 := norm_sub_norm_le (c * (l : ℂ) ^ (2 * e) / α) (-α)
      rw [h1, norm_neg, hαn, sub_neg_eq_add, add_comm] at h2
      rw [ha]; exact h2
    have hl3 : (3 : ℝ) ≤ l := by
      have := hp.two_le
      have : 3 ≤ l := by omega
      exact_mod_cast this
    have := hecke_gap (l : ℝ) hl3 e he
    linarith

theorem root_facts :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M →
      (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 :=
  root_facts_of_bound GlobalTheory.T.newform_norm_coeff_prime_le_of_not_dvd_level

end GlobalTheory.Ord2

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (g : Newform (2 * e + 1)) (α : ℂ), l ≠ 2 → 1 ≤ e → ¬ l ∣ g.M → (g.heckePoly l).IsRoot α → ‖ι.symm α‖ = 1 → ‖ι.symm (g.a l)‖ = 1 ∧ ∀ m : ℕ, 1 ≤ m → α ^ m ≠ 1 := by
  first | exact @GlobalTheory.Ord2.root_facts | exact GlobalTheory.Ord2.root_facts | (intros; apply GlobalTheory.Ord2.root_facts <;> assumption)

end
