import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.ThetaGL

namespace GlobalTheory.Published

def HoweDualityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ)
    (μ : kˣ →* ℂˣ), IsSmoothChar μ →
    (∀ (V W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W)
      (τ' : Representation ℂ (GL (Fin n) k) W'), IsSmooth σ → σ.IsIrreducible → IsSmooth τ → τ.IsIrreducible →
      IsSmooth τ' → τ'.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ τ' → Nonempty (τ.Equiv τ')) ∧
    (∀ (V V' W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (GL (Fin r) k) V) (σ' : Representation ℂ (GL (Fin r) k) V')
      (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth σ → σ.IsIrreducible → IsSmooth σ' → σ'.IsIrreducible →
      IsSmooth τ → τ.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ' τ → Nonempty (σ.Equiv σ'))

end GlobalTheory.Published
