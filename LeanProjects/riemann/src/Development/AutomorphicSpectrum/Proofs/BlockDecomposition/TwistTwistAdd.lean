import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem dpow_add_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s s' : ℝ) (x : GL (Fin n) k) : dpow n (s + s') x = dpow n s x * dpow n s' x := by
  simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply]

theorem giso_tw_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  intro k _ _ _ _ n A s s'
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A.V) fun x => ?_⟩
  ext v
  show ((dpow n s' x : ℂˣ) : ℂ) • ((dpow n s x : ℂˣ) : ℂ) • A.ρ x v = ((dpow n (s + s') x : ℂˣ) : ℂ) • A.ρ x v
  rw [dpow_add_apply, smul_smul, Units.val_mul, mul_comm]

end GlobalTheory.CompanionTheory.LeibOrd

end
