import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll

noncomputable section

namespace GlobalTheory.Published

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

def UnlinkedProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s s' : ℕ)
    (π₁ : Irr k r) (π₂ : Irr k t) (d : Fin s → ℕ) (d' : Fin s' → ℕ) (σ : ∀ a, Irr k (d a)) (σ' : ∀ b, Irr k (d' b)),
    IsCuspSupport π₁.π d (fun a => (σ a).π) → IsCuspSupport π₂.π d' (fun b => (σ' b).π) →
    (∀ a b (h : d a = d' b) (α : ℂˣ),
      ¬ Nonempty ((h ▸ σ a : Irr k (d' b)).π.Equiv (twist (σ' b).π (detChar (Fin (d' b)) (unrChar k α))))) →
    (prod₂ π₁.π π₂.π).IsIrreducible

end GlobalTheory.Published

end
