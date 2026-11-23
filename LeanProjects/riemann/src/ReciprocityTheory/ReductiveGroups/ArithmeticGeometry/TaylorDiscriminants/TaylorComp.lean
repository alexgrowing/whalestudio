import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries
open scoped ContDiff

section TayN

variable {n g : ℕ}

def dirsN (k : Fin n × Fin g →₀ ℕ) : Multiset (Fin n × Fin g → ℂ) :=
  (Finsupp.toMultiset k).map fun q => Pi.single q 1

def fctN (k : Fin n × Fin g →₀ ℕ) : ℂ := ∏ q, ((k q).factorial : ℂ)

def tayN (Θ : (Fin n × Fin g → ℂ) → ℂ) : MvPowerSeries (Fin n × Fin g) ℂ :=
  fun k => mD Θ 0 (dirsN k) / fctN k

end TayN

def TaylorCompSt : Prop :=
  ∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 →
    (∀ c : Fin g → ℂ, tay (fun z => f fun i => c i * z i) 0 =
      subst (fun p : Fin 1 × Fin g => C (c p.2) * X p) (tay f 0)) ∧
    tayN (n := 2) (fun z => f fun i => z ((0 : Fin 2), i) + z ((1 : Fin 2), i)) =
      subst (fun p : Fin 1 × Fin g =>
        (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPowerSeries (Fin 2 × Fin g) ℂ)) (tay f 0)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
