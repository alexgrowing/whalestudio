import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def polyBall (n : ℕ) (s : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ cball s}
  mul_mem' := fun ha hb i => add_mem_cball (ha i) (hb i)
  one_mem' := fun i => by simp [cball]
  inv_mem' := fun {x} hx i => by
    have h := hx i
    simpa [cball, Valuation.map_neg] using h

def resChr (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (L : Subgroup (Multiplicative (Fin n → k))) : L →* ℂˣ :=
  (chrA k ψ a).comp L.subtype

def unipIn (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

def ann (ψ : AddChar k Circle) (n : ℕ) (t : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ a ∈ polyBall n t, ψ (a.toAdd ⬝ᵥ x.toAdd) = 1}
  mul_mem' := fun {x y} hx hy a ha => by
    rw [toAdd_mul, dotProduct_add, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  one_mem' := fun a _ => by simp
  inv_mem' := fun {x} hx a ha => by
    rw [toAdd_inv, dotProduct_neg, AddChar.map_neg_eq_inv, hx a ha, inv_one]

end GlobalTheory.CompanionTheory.MirFourier

end
