import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.Published

def GrothendieckRingPolynomial : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)), IsSegmentClass k Z →
      ∃ Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ, Ψ (GrothGL.unit k) = 1 ∧
        (∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
          (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
          (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂), IsSmooth π₁ → IsSmooth π₂ →
            ∀ h : HasFiniteLength (prod₂ π₁ π₂), Ψ (clsGL (prod₂ π₁ π₂) h) = Ψ (clsGL π₁ h₁) * Ψ (clsGL π₂ h₂)) ∧
        ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ

end GlobalTheory.Published

end
