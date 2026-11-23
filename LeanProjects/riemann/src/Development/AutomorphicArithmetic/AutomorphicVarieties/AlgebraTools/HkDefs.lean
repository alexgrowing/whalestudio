import Mathlib

noncomputable section

open MvPolynomial Equiv

namespace UpperTheory.V.AlgebraTools.Hk

variable (R : Type) [CommRing R] (n : ℕ)

def pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2

def De : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - X p.1)

variable {R} in

def NN (q : R) : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - C q * X p.1)

variable {R n}

def alt (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R := ∑ w : Perm (Fin n), Perm.sign w • rename w x

open Classical in

def dd (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  if h : ∃ y, De R n * y = alt x then h.choose else 0

def invSet (w : Perm (Fin n)) : Finset (Fin n × Fin n) := (pairs n).filter fun p => w⁻¹ p.2 < w⁻¹ p.1

def invN (w : Perm (Fin n)) : ℕ := (invSet w).card

variable (n) in

def poin (q : R) : R := ∑ w : Perm (Fin n), q ^ invN w

def IsDual {ι : Type} [Fintype ι] (a b : ι → MvPolynomial (Fin n) R) : Prop :=
  ∀ w : Perm (Fin n), ∑ i, a i * rename w (b i) = if w = 1 then De R n else 0

structure Bern (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] where
  th : MvPolynomial (Fin n) R →ₐ[R] H
  T : Perm (Fin n) → H
  T_one : T 1 = 1
  T_mul : ∀ a b : Fin n, a.val + 1 = b.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ b → T (swap a b * w) = T (swap a b) * T w
  T_sq : ∀ a b : Fin n, a.val + 1 = b.val → T (swap a b) * T (swap a b) = (q - 1) • T (swap a b) + q • (1 : H)
  comm : ∀ a b : Fin n, a.val + 1 = b.val → ∀ j, j ≠ a → j ≠ b → T (swap a b) * th (X j) = th (X j) * T (swap a b)
  relA : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X a) = th (X b) * T (swap a b) + (q - 1) • th (X a)
  relB : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X b) = th (X a) * T (swap a b) - (q - 1) • th (X a)

namespace Bern

variable {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)

def one : H := ∑ w, b.T w

def Faithful : Prop := ∀ x, b.th x * b.one = 0 → x = 0

def sph (V : Type) [AddCommGroup V] [Module R V] [Module H V] [IsScalarTower R H V] : Submodule R V where
  carrier := {v | ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) • v = q • v}
  add_mem' hu hv a c h := by rw [smul_add, hu a c h, hv a c h, smul_add]
  zero_mem' _ _ _ := by rw [smul_zero, smul_zero]
  smul_mem' r v hv a c h := by
    rw [← algebraMap_smul H r v, ← mul_smul, ← Algebra.commutes, mul_smul, hv a c h, algebraMap_smul, algebraMap_smul,
      smul_comm]

theorem rel_of_quad {H : Type} [Ring H] [Algebra R H] {q : R} (hq : IsUnit q) (T x y : H)
    (hT : T * T = (q - 1) • T + q • (1 : H)) (h : T * y * T = q • x) :
    T * x = y * T + (q - 1) • x ∧ T * y = x * T - (q - 1) • x := by
  have cancel : ∀ a c : H, q • a = q • c → a = c := by
    intro a c hac
    obtain ⟨u, rfl⟩ := hq
    have := congrArg (fun z => ((u⁻¹ : Rˣ) : R) • z) hac
    simpa [smul_smul] using this
  constructor
  · apply cancel
    rw [← mul_smul_comm, ← h, ← mul_assoc, ← mul_assoc, hT]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul, h]
    rw [smul_add, smul_comm q (q - 1) x]
    abel
  · apply cancel
    symm
    rw [smul_sub, ← smul_mul_assoc, ← h, mul_assoc (T * y), hT, mul_add, mul_smul_comm,
      mul_smul_comm, mul_one, h, smul_comm q (q - 1) x]
    abel

end Bern

def Bern.std (R : Type) [CommRing R] (n : ℕ) : Bern n (1 : R) (Module.End R (MvPolynomial (Fin n) R)) where
  th := Algebra.lsmul R R _
  T w := (rename w).toLinearMap
  T_one := LinearMap.ext fun x => by simp
  T_mul a b _ w _ := LinearMap.ext fun x => by simp [rename_rename]
  T_sq a b _ := LinearMap.ext fun x => by
    simp [rename_rename, Function.comp_def]
    first | exact rename_id_apply x | exact AlgHom.congr_fun rename_id x
  comm a b _ j ha hb := LinearMap.ext fun x => by simp [swap_apply_of_ne_of_ne ha hb]
  relA a b _ := LinearMap.ext fun x => by simp
  relB a b _ := LinearMap.ext fun x => by simp

end UpperTheory.V.AlgebraTools.Hk

end
