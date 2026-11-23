import Mathlib

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

def Sec (P : Subgroup G) (h : G → ℝ) (f : G → ℂ) : Prop :=
  Continuous f ∧ ∀ p ∈ P, ∀ g, f (p * g) * h g = f g * h (p * g)

structure Setup (P : Subgroup G) (h : G → ℝ) (mu : (G → ℂ) → ℂ) : Prop where
  closed : IsClosed (P : Set G)
  cocpt : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c
  cont : Continuous h
  pos : ∀ g, 0 < h g
  law : ∀ p ∈ P, ∀ g g', h (p * g) * h g' = h g * h (p * g')
  add : ∀ f f', Sec P h f → Sec P h f' → mu (f + f') = mu f + mu f'
  smul : ∀ (c : ℂ) f, Sec P h f → mu (c • f) = c * mu f
  nonneg : ∀ f, Sec P h f → (∀ g, 0 ≤ (f g).re ∧ (f g).im = 0) → 0 ≤ (mu f).re ∧ (mu f).im = 0

def Inv (P : Subgroup G) (h : G → ℝ) (mu : (G → ℂ) → ℂ) (x : G) : Prop := ∀ f, Sec P h f → mu (fun g => f (g * x)) = mu f

def rp {P : Subgroup G} (q : G ⧸ P) : G := (Quotient.out q)⁻¹

def Repr (P : Subgroup G) (h : G → ℝ) (mu : (G → ℂ) → ℂ) [MeasurableSpace (G ⧸ P)] (ν : Measure (G ⧸ P)) : Prop :=
  IsFiniteMeasure ν ∧ ∀ f, Sec P h f → Integrable (fun q => f (rp q) / h (rp q)) ν ∧ mu f = ∫ q, f (rp q) / h (rp q) ∂ν

def ForSet (Q : ∀ {G : Type} [Group G] [TopologicalSpace G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)],
    (G → ℝ) → ((G → ℂ) → ℂ) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] (h : G → ℝ)
    (mu : (G → ℂ) → ℂ), Setup P h mu → Q P h mu

def Riesz : Prop := ForSet fun P _ h mu => ∃ ν, Repr P h mu ν

def InvM : Prop := ForSet fun {G} _ _ P _ h mu => ∀ ν, Repr P h mu ν → ∀ x : G, Inv P h mu x →
  (Continuous fun q : G ⧸ P => h (rp q * x) / h (rp q)) ∧ ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
    ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν

def Few (P : Subgroup G) (h : G → ℝ) (mu : (G → ℂ) → ℂ) (Ω : Set G) : Prop :=
  ∀ g : G, ∃ (U : Set G) (d : ℕ), IsOpen U ∧ g ∈ U ∧ (∀ p ∈ P, ∀ x ∈ U, p * x ∈ U) ∧ ∀ V ∈ 𝓝 (1 : G), ∀ M : ℕ,
    ∃ γ : Fin M → G, (∀ j, γ j ∈ V ∧ Inv P h mu (γ j)) ∧ ∀ x ∈ U, Set.ncard {j | x * γ j ∉ Ω} ≤ d

def NullC : Prop := ForSet fun {G} _ _ P _ h mu => ∀ ν, Repr P h mu ν → ∀ Ω : Set G, IsOpen Ω →
  (∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) → Few P h mu Ω → ν {q | rp q ∉ Ω} = 0

structure IsCell {N : Type} [AddCommGroup N] [TopologicalSpace N] (P : Subgroup G) (Ω : Set G) (τ : G → N) (w : G)
    (nb : N → G) : Prop where
  isOpen : IsOpen Ω
  left : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x
  right : ∀ y, ∀ x ∈ Ω, x * nb y ∈ Ω ∧ τ (x * nb y) = τ x + y
  cont : ContinuousOn τ Ω
  nbCont : Continuous nb
  nbAdd : ∀ x y, nb (x + y) = nb x * nb y

def OnCell {N : Type} (h : G → ℝ) (Ω : Set G) (τ : G → N) (w : G) (nb : N → G) (f : G → ℂ) : Prop :=
  ∀ x ∈ Ω, f x * h (w * nb (τ x)) = f (w * nb (τ x)) * h x

def CellFormula : Prop := ForSet fun {G} _ _ P _ h mu => ∀ ν, Repr P h mu ν → ∀ (N : Type) [AddCommGroup N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [T2Space N] [LocallyCompactSpace N] [SecondCountableTopology N]
  [MeasurableSpace N] [BorelSpace N] (lam : Measure N) [lam.IsAddHaarMeasure] (Ω : Set G) (τ : G → N) (w : G) (nb : N → G),
  IsCell P Ω τ w nb → (∀ y, Inv P h mu (nb y)) →
  (∀ y, ∀ x ∈ Ω, h (x * nb y) * h (w * nb (τ x)) = h (w * nb (τ x + y)) * h x) → ν {q | rp q ∉ Ω} = 0 →
  ∃ c : ℝ≥0, ∀ f, Sec P h f → OnCell h Ω τ w nb f →
    Integrable (fun y => f (w * nb y)) (c • lam) ∧ mu f = ∫ y, f (w * nb y) ∂(c • lam)

end PositivityTheory.Rg.Rsw.Cell
