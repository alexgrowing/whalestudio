import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open PositivityTheory.RgJS

namespace UpperTheory.ConvolutionTheory.R

def dre {W : Type} (q : W → ℕ) {A B : Type} [Fintype A] [Fintype B] (α : W → A → ℂ) (β : W → B → ℂ) (σ : ℝ) : ℝ :=
  (∑' p, lterm q α β σ p).re

structure Cover (l : ℕ) {W W' : Type} (q : W → ℕ) (q' : W' → ℕ) (u : W' → W) (f : W' → ℕ) (c : W → ℂ) : Prop where
  norm : ∀ w, q' w = q (u w) ^ f w
  fib : ∀ v, (Nat.card {w // u w = v} = l ∧ (∀ w, u w = v → f w = 1) ∧ c v = 1) ∨
    (Nat.card {w // u w = v} = 1 ∧ (∀ w, u w = v → f w = l) ∧ IsPrimitiveRoot (c v) l)

theorem Cover.triv {W : Type} (q : W → ℕ) : Cover 1 q q id (fun _ => 1) (fun _ => 1) :=
  ⟨fun _ => (pow_one _).symm, fun v => Or.inl ⟨by simp, fun _ _ => rfl, rfl⟩⟩

def OrderAsym : Prop := ∀ (F : ℂ → ℂ) (S : ℝ → ℂ) (δ : ℕ), AnalyticAt ℂ F 1 →
  (∀ σ₁ : ℝ, 1 < σ₁ → ∃ M : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ‖S σ‖ ≤ M) →
  (∀ σ : ℝ, 1 < σ → F σ = ((σ : ℂ) - 1) ^ δ * Complex.exp (S σ)) →
    ∃ (k : ℕ) (M : ℝ), ∀ σ : ℝ, 1 < σ → σ ≤ 2 → |(S σ).re - ((δ : ℝ) - k) * (-Real.log (σ - 1))| ≤ M

open Classical in

def ExpRight : Prop := ForSys fun q X _ A => ∀ x y : X, ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧ ∀ σ : ℝ, 1 < σ →
  F σ = ((σ : ℂ) - 1) ^ (if x = y then 1 else 0) * Complex.exp (∑' p, lterm q (A x) (A y) σ p)

open Classical in

def LogAsym : Prop := ForSys fun q X _ A => ∀ x y : X, ∃ M : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
  |dre q (A x) (A y) σ - (if x = y then -Real.log (σ - 1) else 0)| ≤ M

def ZeroExp : Prop := ForSys fun {W} q X d A => ∀ (ι : Type) [Fintype ι] (x : ι → X × ℝ),
  ∑ i, (d (x i).1 : ℝ) * (x i).2 = 0 →
  (∀ σ : ℝ, 1 < σ → Summable fun p : W × ℕ =>
    ‖lterm q (fun w (a : Σ i, Fin (d (x i).1)) => A (x a.1).1 w a.2 * (q w : ℂ) ^ (-((x a.1).2 : ℂ)))
      (fun w (a : Σ i, Fin (d (x i).1)) => A (x a.1).1 w a.2 * (q w : ℂ) ^ (-((x a.1).2 : ℂ))) σ p‖) → ∀ i, (x i).2 = 0

def BCSum : Prop := ∀ (l : ℕ) (W W' : Type) (q : W → ℕ) (q' : W' → ℕ) (u : W' → W) (f : W' → ℕ) (c : W → ℂ), 1 ≤ l →
  (∀ v, 1 ≤ q v) → Cover l q q' u f c → ∀ (A B A' B' : Type) [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (α : W → A → ℂ) (β : W → B → ℂ) (ξ : W' → A' → ℂ) (ζ : W' → B' → ℂ) (σ : ℝ),
    (∀ w (k : ℕ), ∑ a, ξ w a ^ k = ∑ a, α (u w) a ^ (f w * k)) → (∀ w (k : ℕ), ∑ b, ζ w b ^ k = ∑ b, β (u w) b ^ (f w * k)) →
    (Summable fun p => ‖lterm q α β σ p‖) → (Summable fun p => ‖lterm q' ξ ζ σ p‖) ∧
      ∑' p, lterm q' ξ ζ σ p = ∑ j ∈ Finset.range l, ∑' p, lterm q α (fun v b => β v b * c v ^ j) σ p

open Classical in

def AbsCount : Prop := ∀ (l : ℕ) (W W' : Type) (q : W → ℕ) (q' : W' → ℕ) (u : W' → W) (f : W' → ℕ) (c : W → ℂ), 1 ≤ l →
  Cover l q q' u f c → ∀ (X X' : Type) (d : X → ℕ) (d' : X' → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) (A' : ∀ x, W' → Fin (d' x) → ℂ),
    Sys q X d A → Sys q' X' d' A' → ∀ (ι : Type) [Fintype ι] (x : X) (y : ℕ → X) (z : ι → X' × ℝ) (t t' : ℝ),
    (∀ j v, Finset.univ.val.map (A (y j) v) = (Finset.univ.val.map (A (y 0) v)).map (· * c v ^ j)) →
    (∀ w, ∑ i, Finset.univ.val.map (fun a => A' (z i).1 w a * (q' w : ℂ) ^ (-((z i).2 : ℂ))) =
      Finset.univ.val.map fun a => (A x (u w) a * (q (u w) : ℂ) ^ (-(t : ℂ))) ^ f w) →
    (∀ w, ∑ i, Finset.univ.val.map (fun a => A' (z i).1 w a * (q' w : ℂ) ^ (-((z i).2 : ℂ))) =
      Finset.univ.val.map fun a => (A (y 0) (u w) a * (q (u w) : ℂ) ^ (-(t' : ℂ))) ^ f w) →
    t = t' ∧ (∀ i, (z i).2 = t) ∧
      ((Finset.range l).filter fun j => x = y j).card = (Finset.univ.filter fun p : ι × ι => (z p.1).1 = (z p.2).1).card

end UpperTheory.ConvolutionTheory.R
