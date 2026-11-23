import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.FInvIff

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

def TSpan : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], ∃ l : List (𝓞 L)ˣ, ∀ t : InfinitePlace L → ℝ,
    t ∈ Submodule.span ℝ (insert (fun _ => (1 : ℝ)) {x | ∃ u ∈ l, lg u = x})

def TScal : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ),
    (∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t') ∧
    (∀ (t : InfinitePlace L → ℝ) (x : Gp L N), sc t * x = x * sc t) ∧
    (∀ u : (𝓞 L)ˣ, actL (emb L N (GeneralLinearGroup.scalar (Fin N) u)) = actL (sc (N := N) (lg u))) ∧
    (∀ s : InfinitePlace L → ℂˣ, actL (scal L N s) = actL (sc (N := N) fun w => Real.log ‖(s w : ℂ)‖)) ∧
    Continuous fun t : InfinitePlace L → ℝ => actL (sc (N := N) t)

def TSimp : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ),
    (∀ (y : Fin (q + 1) → Pos L N) (t : Fin q → ℝ), (∀ j, 0 ≤ t j) → ∑ j, t j ≤ 1 →
      (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) ∈ Pos L N) ∧
    ∀ (ω : Form (HS L N) q) (g : Gp L N), FInv ω g → ∀ y : Fin (q + 1) → Pos L N,
      intP ω (fun j => g • y j) = intP ω y

def TAv : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (v : InfinitePlace L → ℝ) (ω : Form (HS L N) q),
    ContinuousOn ω (Pos L N) →
    ContinuousOn (av v ω) (Pos L N) ∧
    (∀ g : Gp L N, (∀ t, sc t * g = g * sc t) → ∀ h ∈ Pos L N, pb g (av v ω) h = av v (pb g ω) h) ∧
    (v ∈ Fix ω → ∀ σ : ℝ, σ • v ∈ Fix (av v ω)) ∧
    (∀ y : Fin (q + 1) → Pos L N, Continuous fun τ : ℝ => intP ω fun j => (sc (τ • v) : Gp L N) • y j) ∧
    (∀ y : Fin (q + 1) → Pos L N, intP (av v ω) y = ∫ τ in (0 : ℝ)..1, intP ω fun j => (sc (τ • v) : Gp L N) • y j) ∧
    ∀ x : Gp L N, fr (av v ω) x = ∫ τ in (0 : ℝ)..1, fr ω (sc (τ • v) * x)

end PositivityTheory.KB.CentralizerFixed

end
