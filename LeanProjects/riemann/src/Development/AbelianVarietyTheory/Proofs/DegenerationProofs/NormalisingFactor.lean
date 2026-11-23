import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingPropertiesStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.SymLift

theorem odd_root_iff {U : Type} [CommGroup U] (j : ℕ) (E P w : U) (h : E ^ (2 * j + 1) = P ^ 2) :
    w = P / E ^ j ↔ (w ^ 2 = E ∧ w ^ (2 * j + 1) = P) := by
  constructor
  · rintro rfl
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_pow] at h'
    constructor
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -h'
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -(j • h')
  · rintro ⟨rfl, rfl⟩
    rw [← pow_mul, pow_succ, mul_div_cancel_left]

variable {O : Type} [CommRing O] (N : NumD O)

theorem tk_pow {k : ℕ} (p p' : N.QT k) :
    N.tk p p' ^ k = N.τ p.1.1.toAdd p'.1.1.toAdd *
      (cubN N.θ k 1 p.1.2.b (p'.1.2.b ^ k) * cubN N.θ k 1 p'.1.2.b p.1.2.b ^ k) := by
  have a := NumD.Gt.pow_s p.1.2 k p'.1.1.toAdd
  rw [N.mem_QT.1 p.2, NumD.io_s, ← N.QT_pow_b p'] at a
  rw [NumD.tk, mul_pow, ← a, mul_assoc]

theorem tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have a := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b p''] at a
  change p.1.2.s p''.1.1.toAdd * p'.1.2.s p''.1.1.toAdd / N.θ (N.c p''.1.1.toAdd) p.1.2.b p'.1.2.b *
    cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  replace a := congrArg Additive.ofMul a
  apply Additive.ofMul.injective
  simp only [NumD.tk, ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) a

theorem tk_one_left {k : ℕ} (p : N.QT k) : N.tk 1 p = 1 := by
  change 1 * cubN N.θ k 1 p.1.2.b 1 = 1
  rw [N.cub.N_one, one_mul]

theorem wQ_iff {k : ℕ} (hk : Odd k) (p : N.QT k) (w : Oˣ) :
    w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧
      w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b) := by
  obtain ⟨j, rfl⟩ := hk
  have e : N.wQ p = N.ψ p.1.1.toAdd * mulq N.θ N.σ (2 * j + 1) p.1.2.b /
      (N.tk p p / dbl N.θ N.σ p.1.2.b ^ (2 * j + 1)) ^ j := by
    have : (2 * j + 1 - 1) / 2 = j := by omega
    simp only [NumD.wQ, NumB.wS, NumD.tk, this]
  rw [e, odd_root_iff, eq_div_iff_mul_eq']
  have a := tk_pow N p p
  have b := (GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N 0 p.1.1.toAdd).1
  have c := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB (2 * j + 1) 0 p.1.2.b 1).2.2.1
  rw [← N.QT_pow_b p] at b
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c ⊢
  linear_combination (norm := module) a + b + c

theorem dbl_mul (x y : N.A) :
    dbl N.θ N.σ (x * y) * (N.θ (x * y) x y * N.θ x x y * N.θ y x y) = dbl N.θ N.σ x * dbl N.θ N.σ y := by
  have a := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB 2 0 x y).2.1
  have c := N.cub.coc x y y x
  rw [N.cub.s12 (x * y), N.cub.s12 x y x, N.cub.s12 x (y * y), N.cub.s12 y y x] at c
  simp only [mulq, cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, one_mul, mul_one,
    N.cub.face, div_one, sq] at a
  rw [N.cub.s12 y y x] at a
  replace a := congrArg Additive.ofMul a
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a c ⊢
  linear_combination (norm := abel) c - a

theorem wQ_mul {k : ℕ} (hk : Odd k) (p p' : N.QT k) :
    N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (wQ_iff N hk p' _).1 rfl
  rw [← div_eq_iff_eq_mul', wQ_iff N hk]
  have k₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).2.2.2.1
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  constructor
  · have t₁ := tk_mul_left N p p' (p * p')
    have t₂ := tk_mul_left N p p' p
    have t₃ := tk_mul_left N p p' p'
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).1
    have w₃ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p').1
    have d := dbl_mul N p.1.2.b p'.1.2.b
    have e : (p * p').1.2.b = p.1.2.b * p'.1.2.b := rfl
    rw [e] at t₁ ⊢
    obtain ⟨j, rfl⟩ := hk
    have : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [this]
    have a₁ := E a₁; have b₁ := E b₁; have k₁ := E k₁; have t₁ := E t₁; have t₂ := E t₂; have t₃ := E t₃
    have w₂ := E w₂; have w₃ := E w₃; have d := E d
    apply Additive.ofMul.injective
    simp only [NumD.wp, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ b₁ k₁ t₁ t₂ t₃ w₂ w₃ d ⊢
    linear_combination (norm := module) a₁ + b₁ - k₁ - t₁ - t₂ - t₃ + w₂ + w₃ + (2 * j + 1) • d
  · have t := tk_pow N p p'
    have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b p'.1.2.b).2.1
    have s := N.ψ_add p.1.1.toAdd p'.1.1.toAdd
    change _ = N.ψ (p.1.1.toAdd + p'.1.1.toAdd) * mulq N.θ N.σ k (p.1.2.b * p'.1.2.b)
    have a₂ := E a₂; have b₂ := E b₂; have k₁ := E k₁; have t := E t; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₂ b₂ k₁ t m s ⊢
    linear_combination (norm := module) a₂ + b₂ - ((k + 1) / 2) • k₁ + t - m - s

theorem wQ_inv {k : ℕ} (hk : Odd k) (p : N.QT k) : N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  rw [← eq_div_iff_mul_eq', eq_comm, wQ_iff N hk]
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have e : (p⁻¹).1.2.b = p.1.2.b⁻¹ := rfl
  constructor
  · have t₁ := tk_mul_left N p p⁻¹ p⁻¹
    have t₂ := tk_mul_left N p p⁻¹ p
    have w₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p⁻¹ p).1
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k 1 1 p).1
    have s := N.σ_inv p.1.2.b
    rw [mul_inv_cancel] at t₁ t₂ w₁
    rw [mul_one, left_eq_mul] at w₂
    rw [w₂] at w₁
    rw [tk_one_left, e] at t₁ t₂
    rw [N.cub.s01 p.1.2.b p.1.2.b p.1.2.b⁻¹, N.cub.s12 p.1.2.b p.1.2.b p.1.2.b⁻¹] at t₂
    rw [e]
    have a₁ := E a₁; have t₁ := E t₁; have t₂ := E t₂; have w₁ := E w₁; have s := E s
    apply Additive.ofMul.injective
    simp only [NumD.wp, dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ t₁ t₂ w₁ s ⊢
    linear_combination (norm := module) a₁ + t₁ - t₂ + w₁ - k • s
  · have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b 1).2.2.2
    have s := N.even p.1.1.toAdd
    rw [← N.QT_pow_b p] at s
    change _ = N.ψ (-p.1.1.toAdd) * mulq N.θ N.σ k p.1.2.b⁻¹
    have a₂ := E a₂; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a₂ m s ⊢
    linear_combination (norm := module) a₂ - m - s

theorem normalising_factor : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p :=
  fun _ _ N _ hk p p' => ⟨wQ_iff N hk p, wQ_mul N hk p p', wQ_inv N hk p⟩

end GlobalTheory.Ex.SymLift
