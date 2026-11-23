import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

def hvE {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) : A :=
  ∏ k, (Matrix.of fun i t : Fin (h k) => ∑ a, x a i.val * y a (Fin.castLE (hh k) t)).det

def hvO {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ) : A :=
  ∏ k, (catM (h k) y x).det

def colH {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : ℕ := (Finset.univ.filter fun t : Fin n => k < ν t).card

theorem colH_le {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : colH ν k ≤ n := by
  unfold colH
  calc (Finset.univ.filter fun t : Fin n => k < ν t).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

abbrev GenR (R : Type*) [CommRing R] (n : ℕ) : Type _ := MvPolynomial (ℕ × Fin n) (MvPolynomial (Fin n × Fin n) R)

def gX (R : Type*) [CommRing R] (n : ℕ) : Fin n → ℕ → GenR R n := fun a i => X (i, a)

def gY (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GenR R n) := fun a t => C (X (a, t))

def yV (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) := fun a t => X (a, t)

def unitM (R : Type*) [CommRing R] {n m : ℕ} (I : Fin m → Fin n) : Matrix (Fin n) (Fin n) R :=
  fun a t => if h : t.val < m then (if a = I ⟨t.val, h⟩ then 1 else 0) else 0

end Formalism.L2.PairingIndexBounds.Ent
