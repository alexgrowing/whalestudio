import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

noncomputable section

open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocalHypotheses

section Generic

variable {G : Type} [Group G] [TopologicalSpace G]

def LocConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  (∀ x ∈ twCent θ d, ∀ y ∈ twCent θ d, x * y = y * x) ∧
  (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0) ∧
  {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
    ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite ∧
  (∀ y : G, twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent θ d) ∧
    (twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ d)) ≠ 0)

def UnitConds (θ : G →* G) (K : Subgroup G) (d : G) (f : G → ℂ) : Prop :=
  f = (K : Set G).indicator 1 ∧ d ∈ K ∧ cptPart (twCent θ d) ≤ K ∧
    ∀ y, y⁻¹ * d * θ y ∈ K → ∃ t ∈ twCent θ d, ∃ k ∈ K, y = t * k

end Generic

section Split

variable {H : Type} [Group H]

def swTw (σ : H →* H) : H × H →* H × H :=
  (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom

@[simp] theorem swTw_apply (σ : H →* H) (y : H × H) : swTw σ y = (σ y.2, σ y.1) := rfl

theorem mem_twCent_swTw (σ : H →* H) (hσ : ∀ g, σ (σ g) = g) (d d' : H) (g : H × H) :
    g ∈ twCent (swTw σ) (d, d') ↔
      g.1 ∈ twCent (MonoidHom.id H) (d * σ d') ∧ g.2 = d' * σ g.1 * d'⁻¹ := by
  obtain ⟨g₁, g₂⟩ := g
  show (g₁, g₂) * (d, d') = (d, d') * (σ g₂, σ g₁) ↔ g₁ * (d * σ d') = d * σ d' * g₁ ∧ g₂ = d' * σ g₁ * d'⁻¹
  simp only [Prod.mk_mul_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have e : g₂ = d' * σ g₁ * d'⁻¹ := by rw [← h₂]; group
    refine ⟨?_, e⟩
    rw [← mul_assoc, h₁, e]
    simp only [map_mul, map_inv, hσ]
    group
  · rintro ⟨h₁, rfl⟩
    refine ⟨?_, by group⟩
    simp only [map_mul, map_inv, hσ]
    have : g₁ * d = d * σ d' * g₁ * (σ d')⁻¹ := by
      rw [← h₁]; group
    rw [this]; group

end Split

section Place

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E]

def sgP (a b : ℕ) (w : Pl E) : GLw a w × GLw b w →* GLw a w × GLw b w :=
  (thetaGL a (RingHom.id _)).prodMap (thetaGL b (RingHom.id _))

def ratW (n : ℕ) (w : Pl E) : GL (Fin n) E →* GLw n w := GeneralLinearGroup.map (algebraMap E (w.adicCompletion E))

end Place

end GlobalTheory.CompanionTheory.LocalHypotheses

end
