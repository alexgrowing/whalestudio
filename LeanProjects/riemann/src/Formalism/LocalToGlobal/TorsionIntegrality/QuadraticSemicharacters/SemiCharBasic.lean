import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def OpUMul : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (x y : V) (F : V → ℂ) (z : V),
    opU H x (opU H y F) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) * opU H (x + y) F z

def OpUComm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (F : V → ℂ) (z : V),
    opU H 0 F z = F z ∧ ∀ x y : V,
    opU H x (opU H y F) z
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * opU H y (opU H x F) z

def OpUNorm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (x : V) (F : V → ℂ) (z : V),
    ‖opU H x F z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re)
      = ‖F (z + x)‖ ^ 2 * Real.exp (-Real.pi * (H (z + x) (z + x)).re)

def OpUIsom : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V →ₗ[ℂ] W), IsIsom H H' g → ∀ (x : V) (G : W → ℂ) (z : V),
    opU H x (fun v => G (g v)) z = opU H' (g x) G (g z)

def PullOpU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (δ : V ≃ₗ[ℂ] V), IsIsom H H (δ : V →ₗ[ℂ] V) →
    ∀ (x : V) (F : V → ℂ) (z : V), pullInv δ (opU H x F) z = opU H (δ x) (pullInv δ F) z

def SemiCharBasic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ α → α 0 = 1 ∧ (∀ x ∈ Λ, α (-x) = α x) ∧ Λ ≤ dualLat H Λ

def SemiHom : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ α → ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ (F : V → ℂ) (z : V),
      α x * opU H x (fun v => α y * opU H y F v) z = α (x + y) * opU H (x + y) F z

def OpUAnalytic : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) (x : V)
    (F : V → ℂ), AnalyticOnNhd ℂ F Set.univ → AnalyticOnNhd ℂ (opU H x F) Set.univ

def MatHBasic : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ),
    (∀ z w : n → ℂ, matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j)) ∧ (h.IsHermitian → IsHerm (matH h))

def StdHBasic : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n],
    (∀ z w : n → ℂ, stdH L n z w = ∑ i, Formalism.L2.Th1.F.herm L (z i) (w i)) ∧ IsHerm (stdH L n) ∧
      IsPosDef (stdH L n)

def OpUStd : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] (x : n → ℂ) (f : n → ℂ → ℂ) (z : n → ℂ),
    opU (stdH L n) x (prodFn f) z = ∏ i, Formalism.L2.Th1.F.opU L (x i) (f i) (z i)

def OpUBlk4 : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ),
    (∀ z w : Fin 4 × n → ℂ, matH (blk4 h) z w = ∑ a, matH h (slice a z) (slice a w)) ∧
    ∀ (x : Fin 4 × n → ℂ) (θ : Fin 4 → (n → ℂ) → ℂ) (z : Fin 4 × n → ℂ),
      opU (matH (blk4 h)) x (fun v => ∏ a, θ a (slice a v)) z = ∏ a, opU (matH h) (slice a x) (θ a) (slice a z)

end Formalism.L2.Th1.H
