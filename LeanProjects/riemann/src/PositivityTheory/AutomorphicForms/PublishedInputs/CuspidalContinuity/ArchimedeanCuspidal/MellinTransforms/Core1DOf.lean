import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
import GroundTheory.GlobalFields.TateThesis.ConductorIdeal
import GroundTheory.GlobalFields.TateThesis.HeckeChar

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Complex
open GroundTheory.Global
open scoped NumberField.AdeleRing

namespace Ad3.GM

def gk (ε w : ℝ) : ℝ := Real.exp (-(w ^ 2) / (4 * ε)) / Real.sqrt (4 * Real.pi * ε)

def PLStrip : Prop :=
  ∀ (a b B : ℝ) (M : ℂ → ℂ), a < b → Differentiable ℂ M →
    (∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖M s‖ ≤ C * Real.exp (C * s.im ^ 2)) →
    (∀ s : ℂ, s.re = a → ‖M s‖ ≤ B) → (∀ s : ℂ, s.re = b → ‖M s‖ ≤ B) →
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖M s‖ ≤ B

def GaussK : Prop :=
  ∀ (a : ℝ) (φ : ℝ → ℂ), Integrable (fun z => φ z * (Real.exp (a * z) : ℂ)) → ∀ ε : ℝ, 0 < ε → ∀ y : ℝ,
    ∫ t : ℝ, (∫ z : ℝ, φ z * Complex.exp ((a + t * I) * z)) *
        Complex.exp (ε * (a + t * I) ^ 2 - (a + t * I) * y) =
      2 * Real.pi * ∫ z : ℝ, φ z * (gk ε (z - y) : ℂ)

def Shift : Prop :=
  ∀ (a b B : ℝ) (M : ℂ → ℂ), a < b → Differentiable ℂ M → (∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖M s‖ ≤ B) →
    ∀ ε : ℝ, 0 < ε → ∀ y : ℝ,
      ∫ t : ℝ, M (a + t * I) * Complex.exp (ε * (a + t * I) ^ 2 - (a + t * I) * y) =
        ∫ t : ℝ, M (b + t * I) * Complex.exp (ε * (b + t * I) ^ 2 - (b + t * I) * y)

def ApproxId : Prop :=
  ∀ (a : ℝ) (φ : ℝ → ℂ), Continuous φ → Integrable (fun z => φ z * (Real.exp (a * z) : ℂ)) → ∀ y : ℝ,
    Tendsto (fun ε => ∫ z : ℝ, φ z * (gk ε (z - y) : ℂ)) (𝓝[>] 0) (𝓝 (φ y))

def Core1D : Prop :=
  ∀ σ : ℝ, 0 < σ → ∀ φ₁ φ₂ : ℝ → ℂ, Continuous φ₁ → Continuous φ₂ →
    Integrable (fun y => φ₁ y * (Real.exp (σ * y) : ℂ)) → Integrable (fun y => φ₂ y * (Real.exp (-σ * y) : ℂ)) →
    ∀ M : ℂ → ℂ, Differentiable ℂ M → Ord M (-σ) →
    (∀ s : ℂ, s.re = σ → M s = ∫ y : ℝ, φ₁ y * Complex.exp (s * y)) →
    (∀ s : ℂ, s.re = -σ → M s = ∫ y : ℝ, φ₂ y * Complex.exp (s * y)) → φ₁ = φ₂

def Core1D_of : Prop := PLStrip → GaussK → Shift → ApproxId → Core1D

abbrev emb : ℚˣ →* IdeleGroup ℚ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom

def per (f : IdeleGroup ℚ → ℂ) (x : IdeleGroup ℚ) : ℂ := ∑' a : ℚˣ, f (emb a * x)

def pt (y : ℝ) (z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : IdeleGroup ℚ :=
  moduleSection Rat.infinitePlace (expPos y) * IdeleGroup.ofFinite z

def SumB (f : IdeleGroup ℚ → ℂ) : Prop :=
  ∀ K : Set (IdeleGroup ℚ), IsCompact K → ∃ b : ℚˣ → ℝ, Summable b ∧ ∀ a : ℚˣ, ∀ x ∈ K, ‖f (emb a * x)‖ ≤ b a

def phi (f : IdeleGroup ℚ → ℂ) (c : HeckeCharacter ℚ) (y : ℝ) : ℂ :=
  ∫ z in (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    per f (pt y z) * (c.toIdele (IdeleGroup.ofFinite z) : ℂ) ∂finiteIdeleMeasure ℚ

def PerStep : Prop :=
  ∀ f : IdeleGroup ℚ → ℂ, Continuous f → SumB f → Continuous (per f) ∧ ∀ a x, per f (emb a * x) = per f x

def Unfold : Prop :=
  ∀ F : IdeleGroup ℚ → ℂ, Integrable F (ideleMeasure ℚ) →
    ∫ x, F x ∂ideleMeasure ℚ = ∫ y : ℝ, ∫ z in (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      ∑' a : ℚˣ, F (emb a * pt y z) ∂finiteIdeleMeasure ℚ

def UnfoldL : Prop :=
  ∀ F : IdeleGroup ℚ → ENNReal, Measurable F →
    ∫⁻ x, F x ∂ideleMeasure ℚ = ∫⁻ y : ℝ, ∫⁻ z in (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      ∑' a : ℚˣ, F (emb a * pt y z) ∂finiteIdeleMeasure ℚ

def ArchTriv : Prop :=
  (∀ c : HeckeCharacter ℚ, IsOfFinOrder c → ∀ y z, c.toIdele (pt y z) = c.toIdele (IdeleGroup.ofFinite z)) ∧
  (∀ c : HeckeCharacter ℚ, ∀ a x, c.toIdele (emb a * x) = c.toIdele x) ∧
  (∀ a x, IdeleGroup.ideleModule ℚ (emb a * x) = IdeleGroup.ideleModule ℚ x) ∧
  ∀ y, ∀ z ∈ finiteIntegralUnits ℚ, (IdeleGroup.ideleModule ℚ (pt y z) : ℝ) = Real.exp y

def PhiCont : Prop :=
  ∀ f : IdeleGroup ℚ → ℂ, Continuous (per f) → ∀ c : HeckeCharacter ℚ, Continuous (phi f c)

def PhiStep : Prop :=
  ∀ f : IdeleGroup ℚ → ℂ, Continuous f → SumB f → ∀ τ : ℝ,
    Integrable (fun x => ‖f x‖ * (IdeleGroup.ideleModule ℚ x : ℝ) ^ τ) (ideleMeasure ℚ) →
    ∀ c : HeckeCharacter ℚ, IsOfFinOrder c →
      Continuous (phi f c) ∧ Integrable (fun y => phi f c y * (Real.exp (τ * y) : ℂ)) ∧
      ∀ s : ℂ, s.re = τ → ∫ x, f x * (c.toIdele x : ℂ) * ((IdeleGroup.ideleModule ℚ x : ℝ) : ℂ) ^ s ∂ideleMeasure ℚ =
        ∫ y : ℝ, phi f c y * Complex.exp (s * y)

def Phi_of : Prop := PerStep → Unfold → UnfoldL → ArchTriv → PhiCont → PhiStep

def ExtStep : Prop :=
  ∀ χ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ →* Circle, (∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, χ u = 1) →
    ∃ c : HeckeCharacter ℚ, IsOfFinOrder c ∧ ∀ z ∈ finiteIntegralUnits ℚ, c.toIdele (IdeleGroup.ofFinite z) = χ z

def FourStep : Prop :=
  ∀ Δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ, Continuous Δ →
    (∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, ∀ z, Δ (z * u) = Δ z) →
    (∀ χ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ →* Circle, (∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, χ u = 1) →
      ∫ z in (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ), Δ z * (χ z : ℂ) ∂finiteIdeleMeasure ℚ = 0) →
    Δ 1 = 0

def SepStep : Prop :=
  ∀ f₁ f₂ : IdeleGroup ℚ → ℂ, Continuous (per f₁) → Continuous (per f₂) →
    (∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, ∀ x,
      f₁ (x * IdeleGroup.ofFinite u) = f₁ x ∧ f₂ (x * IdeleGroup.ofFinite u) = f₂ x) →
    (∀ c : HeckeCharacter ℚ, IsOfFinOrder c → phi f₁ c 0 = phi f₂ c 0) → per f₁ 1 = per f₂ 1

def Sep_of : Prop := ExtStep → FourStep → SepStep

def Mellin_of : Prop := PerStep → PhiStep → Core1D → SepStep → Mellin

end Ad3.GM
