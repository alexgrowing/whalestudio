import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoord

noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

section ShortSpan

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def ShortSpan (S : HSpace E) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
    Submodule.span E {x | x ∈ L ∧ meanAbs (S.hT x x) ≤ ρ} = ⊤

theorem shortFrame_of_span (S : HSpace E) (q : ℕ) (ρ : ℝ) (h : ShortSpan S q ρ) : ShortFrame S q ρ := by
  intro L hL hq
  set s : Set S.V := {x | x ∈ L ∧ meanAbs (S.hT x x) ≤ ρ} with hs
  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent E s
  have htop : ⊤ ≤ Submodule.span E (Set.range ((↑) : t → S.V)) := by
    rw [Subtype.range_coe, htsp, hs, h L hL hq]
  let B : Module.Basis t E S.V := Module.Basis.mk hti htop
  let b : Module.Basis (Fin S.rank) E S.V := B.reindex (B.indexEquiv S.frame)
  have hb : ∀ c, b c ∈ s := fun c ↦ by
    simp only [b, Module.Basis.reindex_apply, B, Module.Basis.mk_apply]
    exact hts (Subtype.prop _)
  exact ⟨b, fun c ↦ (hb c).1, fun c ↦ (hb c).2⟩

end ShortSpan

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
