import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open PositivityTheory.RgJS

namespace UpperTheory.V.Z.Tf.GOne

open Classical in

def ExtId : Prop := ForSys fun q X _ A => ∀ x y : X, ∃ F : ℂ → ℂ, (∀ σ : ℝ, 0 < σ → AnalyticAt ℂ F σ) ∧
  ∀ σ : ℝ, 1 < σ → F σ = (if x = y then (σ : ℂ) - 1 else 1) * Complex.exp (∑' p, lterm q (A x) (A y) σ p)

def LogTwo : Prop := ForSys fun q X _ A => ∀ x : X, ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
  |(∑' p, lterm q (A x) (A x) σ p).re + Real.log (σ - 1)| ≤ C

def CrossUp : Prop := ForSys fun q X _ A => ∀ x y : X, x ≠ y → ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
  (∑' p, lterm q (A x) (A y) σ p).re ≤ C

def PartCS : Prop := ForSys fun q X _ A => ∀ (x y : X) (I : Set _) (σ : ℝ), 1 < σ →
  ‖∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A y) σ p.1‖ ^ 2 ≤
    (∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re * (∑' p, lterm q (A y) (A y) σ p).re

def ThinBd : Prop := ForSys fun q X _ A => ∀ (x : X) (I : Set _), (∀ w a, ‖A x w a‖ = 1) →
  (Summable fun w : I => (q w : ℝ)⁻¹) → ∃ C : ℝ, ∀ σ : ℝ, 1 < σ →
    ‖∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1‖ ≤ C

def AbsSplit : Prop := ForSys fun q X _ A => ∀ (x : X) (I : Set _), (∀ w a, ‖A x w a‖ = 1) →
  (Summable fun w : I => (q w : ℝ)⁻¹) → ∀ (J : Type) [Fintype J] (y : J → X),
    (∀ w ∉ I, ∀ k : ℕ, ∑ a, A x w a ^ k = ∑ j, ∑ b, A (y j) w b ^ k) → ∃ j, y j = x

end UpperTheory.V.Z.Tf.GOne

end
