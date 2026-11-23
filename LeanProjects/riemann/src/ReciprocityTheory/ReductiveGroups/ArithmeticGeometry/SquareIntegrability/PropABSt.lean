import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

section

variable {ι : Type} [Fintype ι]

open Classical

def paTh (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v

end

open Classical in

def PaIPJetStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (q c : ℕ), 1 ≤ q → ∀ (a : EuclideanSpace ℂ ι) (F G : EuclideanSpace ℂ ι → ℂ),
    F ∈ paPoly c → G ∈ paPoly c → paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G

open Classical in

def PaUnfoldStatement : Prop :=
  Ext.PackingCount → Ext.GaussianTailBound →
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → 0 < R0 →
    (∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)) →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2 →
    ∀ F : EuclideanSpace ℂ ι → ℂ, F ∈ paPoly c →
      Y.l2 q (paTh Y q F) = (paIP q (paTh Y q F) F).re

open Classical in

def PaThIPStatement : Prop :=
  Ext.PackingCount → Ext.GaussianTailBound →
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → 0 < R0 →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2 →
    ∀ F G : EuclideanSpace ℂ ι → ℂ, F ∈ paPoly c → G ∈ paPoly c →
      HasSum (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) (paIP q (paTh Y q F) G)

end

end ReciprocityTheory.ChartRestriction.G.I2
