import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicBetaCompactInduction

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZOnto

variable {k : Type} [Field k]

def rowM {n : ℕ} (g : Mir k (n + 1)) : Fin (n + 1) → k :=
  ((mirabolicProjection k (n + 1) g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)

def perp (ψ : AddChar k Circle) {m : ℕ} (Λ : AddSubgroup (Fin m → k)) : AddSubgroup (Fin m → k) where
  carrier := {b | ∀ l ∈ Λ, ψ (b ⬝ᵥ l) = 1}
  add_mem' {a b} ha hb l hl := by rw [add_dotProduct, AddChar.map_add_eq_mul, ha l hl, hb l hl, one_mul]
  zero_mem' l _ := by simp
  neg_mem' {a} ha l hl := by rw [neg_dotProduct, AddChar.map_neg_eq_inv, ha l hl, inv_one]

open GlobalTheory.BZMir.Fun GlobalTheory.CompanionTheory.BZBeta
open scoped Topology

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Row

end GlobalTheory.CompanionTheory.BZOnto

end
