import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

open Matrix Complex
open GlobalTheory.SW

namespace GlobalTheory.Phase

noncomputable section

def IsMu (c : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ c ^ m = 1

def Ph (c : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ c ^ m = ((‖c‖ : ℝ) : ℂ) ^ m

def Quad {M : Type} [AddCommGroup M] (S : AddSubgroup M) (f : M → ℂ) : Prop :=
  (∀ x ∈ S, IsMu (f x)) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    f (x + y + z) * f x * f y * f z = f (x + y) * f (y + z) * f (x + z) * f 0

variable {κ ι : Type} [Fintype κ] [Fintype ι]

open Classical in

def Shape (φ : Matrix κ ι ℚ → ℂ) : Prop :=
  IsSB φ ∧ ∃ (c : ℂ) (a : Matrix κ ι ℚ) (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ),
    Ph c ∧ Quad S f ∧ ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0

def om (y y' : Matrix κ ι ℚ × Matrix κ ι ℚ) : ℚ := ∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k)

def chr (y x : Matrix κ ι ℚ) : ℂ := cexp (2 * Real.pi * I * ((∑ k, x k ⬝ᵥ y k : ℚ) : ℂ))

structure VacS (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)) (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ)
    (φ : Matrix κ ι ℚ → ℂ) : Prop where
  fg : A.FG
  dual : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, om y y' = m
  norm : ∀ y ∈ A, ‖ε y‖ = 1
  semi : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * cexp (Real.pi * I * ((om y y' : ℚ) : ℂ))
  ord : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ A, ε (m • y) = 1
  sb : IsSB φ
  fix : ∀ y ∈ A, ε y • heisS y.1 y.2 φ = φ

def PV (φ : Matrix κ ι ℚ → ℂ) : Prop := (∃ A ε, VacS A ε φ) ∧ ∀ x, Ph (φ x)

variable {n g : ℕ}

def dup (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) : Matrix (Fin 2) (Fin n × Fin g) ℚ → ℂ := fun x =>
  φ (Matrix.of fun k i => x 0 (k, i)) * φ (Matrix.of fun k i => x 1 (k, i))

def blk (n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin n × Fin g) (Fin n × Fin g) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then τ p.2 q.2 else 0

theorem isMu_one : IsMu 1 := ⟨1, one_pos, one_pow 1⟩

theorem ph_zero : Ph 0 := ⟨1, one_pos, by simp⟩

theorem ph_I : Ph I := ⟨4, by norm_num, by simp [Complex.I_pow_four]⟩

theorem IsMu.mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  calc (a * b) ^ (m * k) = (a ^ m) ^ k * (b ^ k) ^ m := by ring
    _ = 1 := by rw [h, h', one_pow, one_pow, one_mul]

theorem IsMu.inv {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, h⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩

theorem IsMu.norm_eq_one {a : ℂ} (ha : IsMu a) : ‖a‖ = 1 := by
  obtain ⟨m, hm, h⟩ := ha
  have h1 : ‖a‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h1

theorem IsMu.ph {a : ℂ} (ha : IsMu a) : Ph a := by
  obtain ⟨m, hm, h⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [IsMu.norm_eq_one ⟨m, hm, h⟩, Complex.ofReal_one, one_pow, h]

theorem Ph.mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  calc (a * b) ^ (m * k) = (a ^ m) ^ k * (b ^ k) ^ m := by ring
    _ = (((‖a * b‖ : ℝ) : ℂ)) ^ (m * k) := by
      rw [h, h', norm_mul, Complex.ofReal_mul]
      ring

theorem Ph.inv {a : ℂ} (ha : Ph a) : Ph a⁻¹ := by
  obtain ⟨m, hm, h⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h, norm_inv, Complex.ofReal_inv, inv_pow]⟩

def intPairs (κ ι : Type) : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ) :=
  (AddMonoidHom.prodMap (Int.castAddHom ℚ).mapMatrix (Int.castAddHom ℚ).mapMatrix :
    Matrix κ ι ℤ × Matrix κ ι ℤ →+ Matrix κ ι ℚ × Matrix κ ι ℚ).range

theorem pair_int {a b : Matrix κ ι ℚ} (ha : ∀ k i, ∃ z : ℤ, a k i = z) (hb : ∀ k i, ∃ z : ℤ, b k i = z) :
    ∃ z : ℤ, (∑ k, a k ⬝ᵥ b k : ℚ) = z := by
  choose A hA using ha
  choose B hB using hb
  refine ⟨∑ k, ∑ i, A k i * B k i, ?_⟩
  simp [dotProduct, hA, hB]

omit [Fintype κ] [Fintype ι] in

theorem intM_iff_int {x : Matrix κ ι ℚ} : IntM x ↔ ∀ k i, ∃ z : ℤ, x k i = z := by
  unfold IntM
  refine forall_congr' fun k => forall_congr' fun i => ?_
  rw [IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz, eq_intCast]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz, eq_intCast]⟩

open Classical in

def intInd : Matrix κ ι ℚ → ℂ := fun x => if ∀ k i, ∃ z : ℤ, x k i = z then 1 else 0

end

end GlobalTheory.Phase
