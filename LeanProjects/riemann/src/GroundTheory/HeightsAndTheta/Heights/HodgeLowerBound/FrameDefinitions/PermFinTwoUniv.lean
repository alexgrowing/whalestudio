import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

section Roots

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

abbrev RootPoly : Type := MvPolynomial (Ψ × Fin N) ℚ

def weylAct (w : Ψ → Equiv.Perm (Fin N)) (p : Ψ × Fin N) : Ψ × Fin N := (p.1, w p.1 p.2)

def weylSign (w : Ψ → Equiv.Perm (Fin N)) : ℚ :=
  ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)) : ℚ)

def antisym (P : RootPoly Ψ N) : RootPoly Ψ N :=
  ∑ w : Ψ → Equiv.Perm (Fin N), weylSign Ψ N w • rename (weylAct Ψ N w) P

def rhoMono : Ψ × Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => N - 1 - (p.2 : ℕ)

def flagInt (P : RootPoly Ψ N) : ℚ := coeff (rhoMono Ψ N) (antisym Ψ N P)

variable (j : ℕ)

def IsBlockPerm (w : Ψ → Equiv.Perm (Fin N)) : Prop := ∀ τ i, ((w τ i : ℕ) < j ↔ (i : ℕ) < j)

instance (w : Ψ → Equiv.Perm (Fin N)) : Decidable (IsBlockPerm Ψ N j w) := by
  unfold IsBlockPerm; infer_instance

def rhoBlock : Ψ × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => if (p.2 : ℕ) < j then j - 1 - (p.2 : ℕ) else N - 1 - (p.2 : ℕ)

def blockInt (P : RootPoly Ψ N) : ℚ :=
  coeff (rhoBlock Ψ N j)
    (∑ w ∈ Finset.univ.filter (IsBlockPerm Ψ N j), weylSign Ψ N w • rename (weylAct Ψ N w) P)

def la0 (p : Ψ × Fin N) : ℤ := if (p.2 : ℕ) < j then 0 else -1

def c1L (la : Ψ × Fin N → ℤ) : RootPoly Ψ N := -∑ p, (la p : ℚ) • X p

def muPoly : RootPoly Ψ N := ∑ p ∈ Finset.univ.filter (fun p : Ψ × Fin N => ¬ (p.2 : ℕ) < j), X p

def vandBlocks : RootPoly Ψ N :=
  ∏ τ, ∏ ab ∈ Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
    (X (τ, ab.1) - X (τ, ab.2))

def fib (cf : ℚ) : RootPoly Ψ N := C cf * vandBlocks Ψ N j

def fdeg : ℚ := blockInt Ψ N j (vandBlocks Ψ N j)

def dimN : ℕ := Fintype.card Ψ * j * (N - j)

def FA (cf : ℚ) : RootPoly Ψ N := muPoly Ψ N j ^ (dimN Ψ N j + 1) * fib Ψ N j cf

def Jint (cf : ℚ) : ℚ := flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * fib Ψ N j cf)

end Roots

def abelian₂ (B rd Lval : ℝ) : ℝ := Real.log (B * rd) + |Lval|

section Line

theorem perm_fin_two_univ : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
  decide

theorem sum_unit_perm {M : Type*} [AddCommMonoid M] (g : (Unit → Equiv.Perm (Fin 2)) → M) :
    ∑ w, g w = g (fun _ => 1) + g (fun _ => Equiv.swap 0 1) := by
  rw [← (Equiv.funUnique Unit (Equiv.Perm (Fin 2))).symm.sum_comp, perm_fin_two_univ,
    Finset.sum_pair (by decide)]
  rfl

theorem rhoMono_line : rhoMono Unit 2 = Finsupp.single ((), 0) 1 := by
  ext ⟨u, i⟩
  fin_cases i <;> simp [rhoMono, Finsupp.single_apply]

theorem dimN_line : dimN Unit 2 1 = 1 := rfl

theorem muPoly_line : muPoly Unit 2 1 = X ((), 1) := by
  unfold muPoly
  rw [show (Finset.univ.filter fun p : Unit × Fin 2 => ¬ (p.2 : ℕ) < 1) = {((), 1)} by decide]
  simp

theorem vandBlocks_line : vandBlocks Unit 2 1 = 1 := by
  unfold vandBlocks
  rw [show (Finset.univ.filter fun ab : Fin 2 × Fin 2 =>
      ab.1 < ab.2 ∧ ((ab.1 : ℕ) < 1 ↔ (ab.2 : ℕ) < 1)) = ∅ by decide]
  simp

theorem Jint_line (cf : ℚ) : Jint Unit 2 1 cf = -cf := by
  unfold Jint flagInt antisym
  rw [dimN_line, pow_one, muPoly_line, fib, vandBlocks_line, mul_one, sum_unit_perm, rhoMono_line]
  simp only [weylSign, Finset.univ_unique, Finset.prod_singleton, Equiv.Perm.sign_one,
    Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide), map_mul, rename_X, rename_C, coeff_add,
    coeff_smul, smul_eq_mul, weylAct]
  rw [coeff_X_mul', coeff_X_mul']
  simp [coeff_C, Finsupp.single_apply, Equiv.swap_apply_of_ne_of_ne]

theorem fdeg_line : fdeg Unit 2 1 = 1 := by
  unfold fdeg blockInt
  rw [vandBlocks_line]
  rw [show (Finset.univ.filter (IsBlockPerm Unit 2 1)) = {fun _ => 1} by decide]
  have : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  simp [this, weylSign]

theorem FA_line (cf : ℚ) : FA Unit 2 1 cf = C cf * X ((), 1) ^ 2 := by
  unfold FA fib
  rw [dimN_line, muPoly_line, vandBlocks_line]
  ring

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
