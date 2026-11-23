import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open MvPolynomial

noncomputable section

abbrev RootPoly (f N : ℕ) : Type := MvPolynomial (Fin f × Fin N) ℚ

def alternant {R : Type*} [CommRing R] {m : ℕ} (e : Fin m → ℕ) (v : Fin m → R) : R :=
  (Matrix.of fun i j : Fin m => v i ^ e j).det

def staircase (m : ℕ) : Fin m → ℕ := fun j => m - 1 - (j : ℕ)

def blockRoots (f N : ℕ) (τ : Fin f) : Fin N → RootPoly f N := fun i => X (τ, i)

def antisymBlocks (f N : ℕ) (H : RootPoly f N) : RootPoly f N :=
  ∑ w : Fin f → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℚ) • rename (fun p => (p.1, w p.1 p.2)) H

def divDiff (f N : ℕ) (H : RootPoly f N) : RootPoly f N := by
  classical
  exact if h : ∃ P, antisymBlocks f N H = (∏ τ, alternant (staircase N) (blockRoots f N τ)) * P
    then h.choose else 0

def flagInt (f N : ℕ) (H : RootPoly f N) : ℚ := constantCoeff (divDiff f N H)

def blockPsum (f N : ℕ) (k : ℕ) (τ : Fin f) : RootPoly f N := ∑ i : Fin N, X (τ, i) ^ k

inductive SmallCase
  | last
  | first

def smallRoots (f r a : ℕ) : SmallCase → Fin f → Fin r → RootPoly f (r + a)
  | .last, τ, i => X (τ, ⟨a + i, by omega⟩)
  | .first, τ, i => -X (τ, ⟨i, by omega⟩)

def otherRoots (f r a : ℕ) : SmallCase → Fin f → Fin a → RootPoly f (r + a)
  | .last, τ, i => X (τ, ⟨i, by omega⟩)
  | .first, τ, i => X (τ, ⟨r + i, by omega⟩)

def smallMu (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  ∑ τ, ∑ i, smallRoots f r a c τ i

def fibClass (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  ∏ τ, alternant (staircase r) (smallRoots f r a c τ) * alternant (staircase a) (otherRoots f r a c τ)

def restPoly (f r a : ℕ) (c : SmallCase) : RootPoly f (r + a) :=
  smallMu f r a c ^ (f * (r * a) + 1) * fibClass f r a c

def restJ (f r a : ℕ) (c : SmallCase) : ℚ :=
  flagInt f (r + a) (smallMu f r a c ^ (f * (r * a)) * fibClass f r a c)

def IsPsumDecomposition (f N : ℕ) (F : RootPoly f N) (Q : ℕ → Fin f → RootPoly f N) : Prop :=
  F = ∑ k ∈ Finset.Icc 1 N, ∑ τ, blockPsum f N k τ * Q k τ

def termT (f N : ℕ) (Q : ℕ → Fin f → RootPoly f N) (k : ℕ) (τ : Fin f) (G : RootPoly f N) : ℚ :=
  k * flagInt f N (G * Q k τ)

def restAtPrime (f r a : ℕ) (c : SmallCase) (Q : ℕ → Fin f → RootPoly f (r + a))
    (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ) (p : ℕ) : ℝ :=
  Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n' : ℕ,
    ((p : ℝ) ^ ((n' + 1) * k))⁻¹ *
      ((termT f (r + a) Q k τ
        (C (e p (n' + 1) τ k) * ∑ i, smallRoots f r a c (s p (n' + 1) τ) i ^ (k - 1)) : ℚ) : ℝ)

def S9.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f r a : ℕ) (c : SmallCase) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    (∃ Q, IsPsumDecomposition f (r + a) (restPoly f r a c) Q) ∧
    ∀ Q : ℕ → Fin f → RootPoly f (r + a), IsPsumDecomposition f (r + a) (restPoly f r a c) Q →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n' τ k, e p n' τ k = 1 ∨ e p n' τ k = -1) → ∀ S : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ S ∧ p.Prime ∧ B₀ < p} => |restAtPrime f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ S ∧ p.Prime ∧ B₀ < p}, restAtPrime f r a c Q s e p| ≤
        C * r * ((f * (r * a) + 1 : ℕ) : ℝ) * |(restJ f r a c : ℝ)|

def inhQ : ℕ → Fin 1 → RootPoly 1 (1 + 1) :=
  fun k _ => if k = 1 then C (2⁻¹ : ℚ) * (X (0, 1) - X (0, 0)) else if k = 2 then C (2⁻¹ : ℚ) else 0

theorem S9.hypotheses_inhabited :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
      IsPsumDecomposition 1 (1 + 1) (restPoly 1 1 1 .last) inhQ ∧
      ∀ (p n' : ℕ) (τ : Fin 1) (k : ℕ), (fun _ _ _ _ => (1 : ℚ)) p n' τ k = 1 ∨
        (fun _ _ _ _ => (1 : ℚ)) p n' τ k = -1 := by
  refine ⟨by norm_num, ?_, fun _ _ _ _ => Or.inl rfl⟩
  have hI : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  simp only [IsPsumDecomposition, restPoly, smallMu, fibClass, alternant, smallRoots,
    otherRoots, hI, inhQ, blockPsum, Matrix.det_unique, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton]
  rw [Finset.sum_pair (by norm_num)]
  simp [staircase, Fin.sum_univ_succ]
  have h2 : (C (2⁻¹ : ℚ) : RootPoly 1 (1 + 1)) * 2 = 1 := by
    rw [show (2 : RootPoly 1 (1 + 1)) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  linear_combination (-X ((0 : Fin 1), (1 : Fin (1 + 1))) ^ 2) * h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
