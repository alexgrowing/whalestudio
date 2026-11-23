import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

def dpDen (e i n : ℕ) : ℕ := i.factorial * (n / e).factorial

theorem dpDen_pos (e i n : ℕ) : 0 < dpDen e i n := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

section Q

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def ofW (w : ℕ × ℕ → Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ =>
  PowerSeries.mk fun i => PowerSeries.mk fun n => algebraMap O K (emb t τ (w (i, n))) / (dpDen e i n : K)

def QSet : Set (ZMod a → K⟦X⟧⟦X⟧) := Set.range (ofW t K e)

theorem coeff_ofW (w : ℕ × ℕ → Wq l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (ofW t K e w τ)) = algebraMap O K (emb t τ (w (i, n))) / (dpDen e i n : K) := by
  simp [ofW, coeff_mk]

variable {K}

def GoodSet (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {z | z ∈ QSet t K e ∧ frob2 φ₂ z ∈ QSet t K e ∧
    ∃ B ∈ QSet t K e, frob2 φ₂ z = z ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B}

variable (K) in

def cstW (c : Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ => C (C (algebraMap O K (emb t τ c)))

end Q

variable (a : ℕ) (K : Type) [NormedField K]

def uFam : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C X

def dFam (e q : ℕ) : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C (C ((q.factorial : K)⁻¹) * X ^ (e * q))

def xFam (i : ℕ) : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C (C ((i.factorial : K)⁻¹)) * X ^ i

end GlobalTheory.CrysPrism
