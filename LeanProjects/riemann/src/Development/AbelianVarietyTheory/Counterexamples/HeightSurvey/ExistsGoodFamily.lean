import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.S Matrix

namespace GlobalTheory.DefiniteCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jm_const (n : ℕ) (s : Bool) :
    Formalism.REAL.Jm (fun _ : Fin n => s) = (if s then (1 : ℂ) else -1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [Formalism.REAL.Jm, h, Matrix.one_apply]

theorem kset_const (n : ℕ) (s : Bool) : Formalism.REAL.Kset (fun _ : Fin n => s) = UJset (fun _ : Fin n => s) := by
  ext g
  simp only [Formalism.REAL.Kset, UJset, Formalism.REAL.inUJ, jm_const, Set.mem_setOf_eq, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  cases s <;> simp

theorem lowK_const (n : ℕ) (s : Bool) (lam : Fin n → ℝ) (a : Fin n) :
    Formalism.QuantumDeterminants.lowK (fun _ : Fin n => s) lam a = lam a - (((n : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ n := a.2
  simp only [Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show n - 1 - (a : ℕ) = n - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem isDS_const_top {n : ℕ} {s : Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsDS (fun _ => s) lam σ) :
    IsKTypeOf (fun _ => s) σ (Formalism.QuantumDeterminants.lowK (fun _ => s) lam) ⊤ := by
  obtain ⟨_, _, _, hirr, _, ⟨S, hS⟩, _⟩ := h
  have hfd := hS.1
  rcases hirr S S.closed_of_finiteDimensional (fun g hg v hv => hS.2.1 g (by rwa [kset_const]) v hv) with h0 | h1
  · obtain ⟨v, hv, hv0, _⟩ := hS.2.2.2.1
    exact absurd (by simpa [h0] using hv) hv0
  · rwa [h1] at hS

end GlobalTheory.DefiniteCheck

end
