import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions Finset

section
variable {p : ℕ} [Fact p.Prime]

end

section
variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

end

section LeafEx

variable {K : Type} [Field K] (p : ℕ) {h : ℕ}

def PhiL (t : Fin h → PowerSeries K) : Fin h → PowerSeries K := fun i => PowerSeries.mk fun n =>
  (if i.val = 0 ∧ n = 1 then 1 else 0) -
    ∑ k ∈ Ico 1 (n + 1), PowerSeries.coeff n ((t (FormalGroupSystem.posSub i k)) ^ (p ^ (2 * k))) / (p : K) ^ k

def TL : ℕ → Fin h → PowerSeries K
  | 0 => fun _ => 0
  | N + 1 => PhiL p (TL N)

def tL (i : Fin h) : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff n (TL p n i : PowerSeries K)

end LeafEx

section LeafUn

variable {K : Type} [Field K] (p : ℕ) {h : ℕ}

end LeafUn

section
variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

def eXY (m : ℕ × ℕ →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (∑ x ∈ m.support, m x * x.1) + Finsupp.single 1 (∑ x ∈ m.support, m x * x.2)

end
section
variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

end

section
variable (p : ℕ) {Kc : Type} [Field Kc]

end

section
variable {Kc : Type} [Field Kc] (Oc : Subring Kc)

variable (p : ℕ)

end

section
variable {p : ℕ} {Kc : Type} [Field Kc] {Oc : Subring Kc}

theorem deg2 (n : Fin 2 →₀ ℕ) : n.degree = n 0 + n 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

def DD (p : ℕ) (Oc : Subring Kc) (vp : Kc) (H : MvPowerSeries (Fin 2) Kc) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, vp ^ n.degree * (p : Kc) ^ (n 1 / p) * MvPowerSeries.coeff n H ∈ Oc

end

end Formalism.MainNotions.KernelEntryData
