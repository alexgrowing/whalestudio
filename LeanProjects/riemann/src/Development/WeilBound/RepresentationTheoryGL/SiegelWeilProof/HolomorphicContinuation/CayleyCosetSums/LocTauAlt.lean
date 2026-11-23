import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def fz (m : ℕ) (e : ℤ) (z : ℂ) (x : M2 n) : ℂ :=
  x.det ^ e * (u1 x).det ^ (-(m : ℤ)) * ((u1 x).det * (ub1 x).det) ^ (-z)

def sig (X : M2 n) : M2 n := -((JJ n)⁻¹ * Xᴴ * JJ n)

def rC (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) 0 +
    Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) 0

def lowQ (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 Q 0 1 - 1

def tOp {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (ρ : Kg → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F (x * ι k * a * nU (herm t) * b) * ψ t) ∂μ

def LocTau : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ Q : Matrix (Fin n) (Fin n) ℂ,
    ∃ (N : ℕ) (ρ : Fin N → Kg → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ) (a b : Fin N → M2 n) (D : ℂ → ℂ)
      (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) ∧ (∀ l, IsSingTest (ψ l)) ∧ (∀ l, InG (a l) ∧ InG (b l)) ∧
      Differentiable ℂ D ∧ D 0 ≠ 0 ∧ (∀ l, Differentiable ℂ (M l)) ∧
      ∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ ι (ρ l) (ψ l) (a l) (b l) (fz m e z) x

def spt (y : M2 n) : Matrix (Fin n) (Fin n) ℂ := (Complex.I • y.toBlocks₁₁ + y.toBlocks₁₂) * (u1 y)⁻¹

def SH (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ v : Fin n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ ((1 / (2 * Complex.I)) • (Z - Zᴴ)) *ᵥ v).re}

def HTop : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n →
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (Ht : G → ℝ≥0) (s₀ : ℂ) (sec : G → ℂ),
    Continuous ι →
    (∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
      ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ sec (x * ι y') = S * F0 m 0 e y') →
    ∀ (U : Set ℂ) (κ : ℕ) (Ê : ℂ → G → ℂ) (σ : ℝ), IsOpen U → GlobalTheory.Cont.IsRightDomain U → s₀ ∈ U →
    (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ univ) →
    (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) →
    (∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = (z - s₀) ^ κ * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec x) g) →
    (∀ ψ, IsSingTest ψ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ t, mR (nb t) = nU (herm t)) →
      ∀ (g : G) (a b : GR n), ∫ t, Ê s₀ (g * ι (a * nb t * b)) * ψ t = 0) →
    ∀ g, ∃ h : Matrix (Fin n) (Fin n) ℂ → ℂ, DifferentiableOn ℂ h (SH n) ∧
      ∀ y : GR n, Ê s₀ (g * ι y) = F0 m 0 e y * h (spt (mR y))

end PositivityTheory.Rg.Sw.HSt
