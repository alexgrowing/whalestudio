import Mathlib

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap

def avg {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (B K : Subgroup Λ) (u : S → ℝ) (x : S) : ℝ :=
  ((B.subgroupOf K).index : ℝ)⁻¹ *
    ∑ᶠ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j ((c.out : K) : Λ) * x)

def TwoTr {Λ : Type} [Group Λ] (E K : Subgroup Λ) : Prop :=
  ∀ g ∈ K, g ∉ E → ∀ g' ∈ K, g' ∉ E → ∃ e ∈ E, ∃ e' ∈ E, g' = e * g * e'

def LInv {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S) (E : Subgroup Λ) (u : S → ℝ) : Prop :=
  ∀ γ ∈ E, ∀ x, u (j γ * x) = u x

def Hilb : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (W₁ W₂ W₃ K₁₂ K₁₃ K₂₃ : Submodule ℝ H), IsClosed (W₁ : Set H) → IsClosed (W₂ : Set H) → IsClosed (W₃ : Set H) →
  IsClosed (K₁₂ : Set H) → IsClosed (K₁₃ : Set H) → IsClosed (K₂₃ : Set H) →
  K₁₂ ≤ W₁ ⊓ W₂ → K₁₃ ≤ W₁ ⊓ W₃ → K₂₃ ≤ W₂ ⊓ W₃ →
  (∀ u ∈ W₁, u ∈ K₁₂ᗮ → ∀ u' ∈ W₂, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) →
  (∀ u ∈ W₃, u ∈ K₁₃ᗮ → ∀ u' ∈ W₁, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) →
  (∀ u ∈ W₃, u ∈ K₂₃ᗮ → ∀ u' ∈ W₂, |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖)) →
  ∀ v ∈ W₁ ⊓ W₂, v ∈ (W₁ ⊓ W₂ ⊓ W₃)ᗮ → ∀ w ∈ W₁ ⊓ W₃, |⟪v, w⟫_ℝ| ≤ 2 / 5 * (‖v‖ * ‖w‖)

def Design : Prop := ∀ (Λ S : Type) [Group Λ] [Group S] (j : Λ →* S) (B E E' K : Subgroup Λ), B = E ⊓ E' → E ≤ K →
  E' ≤ K → (B.subgroupOf K).index ≠ 0 → TwoTr E K → 25 ≤ (B.subgroupOf E').index →
  ∀ (a b : S → ℝ), LInv j E a → LInv j E' b → ∀ x, avg j B K a x = 0 →
    avg j B K (fun y => a y * b y) x ^ 2 ≤
      1 / 25 * (avg j B K (fun y => a y ^ 2) x * avg j B K (fun y => b y ^ 2) x)

def Unfold : Prop := ∀ (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  (μ : Measure S) [μ.IsMulLeftInvariant] (j : Λ →* S), Function.Injective j → ∀ (B K : Subgroup Λ), B ≤ K →
  (B.subgroupOf K).index ≠ 0 →
  (∀ u : S → ℝ, LInv j B u → LInv j K (avg j B K u)) ∧ (∀ u : S → ℝ, LInv j K u → avg j B K u = u) ∧
  (∀ u : S → ℝ, Measurable u → Measurable (avg j B K u)) ∧
  (∀ E : Subgroup Λ, B ≤ E → E ≤ K → ∀ u : S → ℝ, LInv j B u → avg j E K (avg j B E u) = avg j B K u) ∧
  ∀ D : Set S, IsFundamentalDomain (K.map j) D μ →
    (∃ D' : Set S, IsFundamentalDomain (B.map j) D' μ) ∧
    ∀ D' : Set S, IsFundamentalDomain (B.map j) D' μ → μ D' = (B.subgroupOf K).index * μ D ∧
      ∀ u : S → ℝ, Measurable u → LInv j B u →
        (IntegrableOn u D' μ ↔ IntegrableOn (avg j B K fun y => |u y|) D μ) ∧
        (IntegrableOn u D' μ → IntegrableOn (avg j B K u) D μ ∧
          ∫ x in D', u x ∂μ = (B.subgroupOf K).index * ∫ x in D, avg j B K u x ∂μ)

def AEConst : Prop := ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
  [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [μ.IsHaarMeasure]
  (A : Subgroup S), Dense (A : Set S) → ∀ u : S → ℝ, Measurable u → (∀ g ∈ A, (fun x => u (g * x)) =ᵐ[μ] u) →
    ∃ c : ℝ, u =ᵐ[μ] fun _ => c

structure Tri {Λ : Type} [Group Λ] (K₀ K₁ K₂ : Subgroup Λ) : Prop where
  fin₀ : ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf K₀).index ≠ 0
  fin₁ : ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf K₁).index ≠ 0
  fin₂ : ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf K₂).index ≠ 0
  two₀ : TwoTr (K₀ ⊓ K₁) K₀
  two₁ : TwoTr (K₁ ⊓ K₂) K₁
  two₂ : TwoTr (K₁ ⊓ K₂) K₂
  big₀₂ : 25 ≤ ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf (K₀ ⊓ K₂)).index
  big₀₁ : 25 ≤ ((K₀ ⊓ K₁ ⊓ K₂).subgroupOf (K₀ ⊓ K₁)).index

def GapAbs : Prop := ∀ (Λ S : Type) [Group Λ] [Countable Λ] [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
  (μ : Measure S) [μ.IsHaarMeasure] (j : Λ →* S), Function.Injective j → ∀ (K₀ K₁ K₂ : Subgroup Λ), Tri K₀ K₁ K₂ →
  Dense (((K₀ ⊔ K₁).map j : Subgroup S) : Set S) → ∀ D₀ D₁ D₂ : Set S, IsFundamentalDomain (K₀.map j) D₀ μ →
  IsFundamentalDomain (K₁.map j) D₁ μ → IsFundamentalDomain (K₂.map j) D₂ μ → μ D₀ < ⊤ → μ D₁ = μ D₀ →
  ∀ w : S → ℝ, Measurable w → LInv j K₁ w → IntegrableOn (fun x => w x ^ 2) D₁ μ → ∫ x in D₁, w x ∂μ = 0 →
    IntegrableOn (fun x => avg j (K₀ ⊓ K₁) K₀ w x ^ 2) D₀ μ ∧ ∫ x in D₀, avg j (K₀ ⊓ K₁) K₀ w x ∂μ = 0 ∧
      ∫ x in D₀, avg j (K₀ ⊓ K₁) K₀ w x ^ 2 ∂μ ≤ (2 / 5 : ℝ) ^ 2 * ∫ x in D₁, w x ^ 2 ∂μ

end PositivityTheory.KB.SpectralGap

end
