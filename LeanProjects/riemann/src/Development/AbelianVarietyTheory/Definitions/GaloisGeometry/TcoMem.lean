import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K] {F : Type} [Field F] [Algebra k F] [Algebra F K] [IsScalarTower k F K]
  {d : ℕ} (x : Fin (d + 1) → F)

theorem tco_mem (j : Fin d) : algebraMap F K (x j.succ / x 0) ∈ rB k K x {0} := by
  have hA : x j.succ / x 0 ∈ rA k x {0} := by
    unfold rA
    exact Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩
  unfold rB
  rw [Subalgebra.mem_restrictScalars]
  exact isIntegral_algebraMap (R := rA k x {0}) (A := K) (x := ⟨_, hA⟩)

def fib : Type := {e : rB k K x {0} →ₐ[k] k // ∀ j, e ⟨_, tco_mem k K x j⟩ = 0}

def locCoch (h : K) : Finset (Fin (d + 1)) → DR k K := fun s => if s = Finset.univ then h • vol0 k K x else 0

end GlobalTheory.PD
