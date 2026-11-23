import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StDiagRatioBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def diagChart {ι ν κ : Type} (c : ∀ k, T.yyIdx ι ν κ k) : ∀ k, T.wwIdx ι ν κ k
  | .base => (c .base : ι)
  | .det => (c .det : ν)
  | .line0 => (c .line : κ)
  | .line1 => (c .line : κ)

theorem coneRatios_wwCoord_diag {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E] [Module Ω E]
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Φ) (c : ∀ k, T.yyIdx ι ν κ k) :
    coneRatios (T.wwCoord x δ e φ a a) (diagChart c) = coneRatios (T.yyCoord x δ e φ a) c := by
  ext r
  constructor
  · rintro ⟨⟨k, i⟩, rfl⟩
    cases k
    · exact ⟨⟨.base, (i : ι)⟩, rfl⟩
    · exact ⟨⟨.det, (i : ν)⟩, rfl⟩
    · exact ⟨⟨.line, (i : κ)⟩, rfl⟩
    · exact ⟨⟨.line, (i : κ)⟩, rfl⟩
  · rintro ⟨⟨k, i⟩, rfl⟩
    cases k
    · exact ⟨⟨.base, (i : ι)⟩, rfl⟩
    · exact ⟨⟨.det, (i : ν)⟩, rfl⟩
    · exact ⟨⟨.line0, (i : κ)⟩, rfl⟩

theorem DiagRatioBasis.proof (hY : YYRatioBasis.Statement) : DiagRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hφ hgF hg ha
  obtain ⟨c, t', hc, hind, hmem, halg⟩ :=
    hY Ω ι ν κ E Φ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htA hδ hδF hφ hgF hg ha
  refine ⟨diagChart c, t', fun k => ?_, hind, ?_, ?_⟩
  · cases k
    exacts [hc .base, hc .det, hc .line, hc .line]
  · rw [coneRatios_wwCoord_diag]; exact hmem
  · rw [coneRatios_wwCoord_diag]; exact halg

end

end GroundTheory.Heights₂.Heights.Inter
