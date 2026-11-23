import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll

noncomputable section

namespace GlobalTheory.Published

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

def DepthZeroJacquetInjective : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ)
    (e : (Σ a, Fin (d a)) ≃ Fin n) (π : Irr k n) (v : π.V),
    v ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) →
    (Submodule.Quotient.mk v : Jacquet π.π (unipRad k e)) = 0 → v = 0

end GlobalTheory.Published

end
