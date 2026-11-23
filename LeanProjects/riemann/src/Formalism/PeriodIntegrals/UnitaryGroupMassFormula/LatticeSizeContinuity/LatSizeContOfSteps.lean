import Mathlib
import Formalism.PeriodIntegrals.LatSizeCont

noncomputable section

open NumberField Matrix
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

def nsq {n : ℕ} (w : Fin n → ℂ) : ℝ := ∑ i, ‖w i‖ ^ 2

def LatIs : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ Λ : Submodule (𝓞 I.E) (Fin I.n → I.E), Λ.FG ∧
    Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤ ∧ Size.latSet I x = (Λ : Set (Fin I.n → I.E))

def LatLoc : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ U ∈ nhds x.2, ∀ x' : I.GA, x'.2 ∈ U → Size.latSet I x' = Size.latSet I x

def DetMono : Prop :=
  ∀ (n j : ℕ) (C : Matrix (Fin n) (Fin j) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (κ : ℝ), 0 ≤ κ →
    (∀ w : Fin n → ℂ, nsq (M *ᵥ w) ≤ κ * nsq w) →
    0 ≤ ((Cᴴ * C).det).re ∧ (((M * C)ᴴ * (M * C)).det).re ≤ κ ^ j * ((Cᴴ * C).det).re

def ArchNear : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (y : I.Ginf) (δ : ℝ), 0 < δ → ∃ U ∈ nhds y, ∀ y' ∈ U, ∀ (v : InfinitePlace I.F) (w : Fin I.n → ℂ),
    nsq ((Formalism.MainNotions.S.uMat (y' v)⁻¹ * Formalism.MainNotions.S.uMat (y v)) *ᵥ w) ≤ (1 + δ) * nsq w ∧
    nsq ((Formalism.MainNotions.S.uMat (y v)⁻¹ * Formalism.MainNotions.S.uMat (y' v)) *ᵥ w) ≤ (1 + δ) * nsq w

def SizeNear : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA) (δ : ℝ), 0 < δ → ∃ U ∈ nhds x, ∀ x' ∈ U,
    (∀ s : Size.Sub I x, ∃ s' : Size.Sub I x', Size.size I s' ≤ (1 + δ) * Size.size I s) ∧
    (∀ s' : Size.Sub I x', ∃ s : Size.Sub I x, Size.size I s ≤ (1 + δ) * Size.size I s')

def SizeNearOf : Prop := LatLoc → DetMono → ArchNear → SizeNear

def MinorEx : Prop :=
  ∀ (E : Type) [Field E] (n j : ℕ) (b : Fin j → Fin n → E), LinearIndependent E b →
    ∃ ι : Fin j → Fin n, Function.Injective ι ∧ (Matrix.of fun a c => b a (ι c)).det ≠ 0

def GramLow : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ c : ℝ, 0 < c ∧ ∀ (v : InfinitePlace I.F) (j : ℕ) (b : Fin j → Fin I.n → I.E)
    (ι : Fin j → Fin I.n), Function.Injective ι →
    c ^ j * ‖I.φ v (Matrix.of fun a d => b a (ι d)).det‖ ^ 2 ≤ ((Size.gramV I x v b).det).re

def GramLowOf : Prop := DetMono → GramLow

def IdxBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∃ D : ℝ, 1 ≤ D ∧
    ∀ (j : ℕ) (b : Fin j → Fin n → E) (ι : Fin j → Fin n) (B : Submodule (𝓞 E) (Fin n → E)),
      (Matrix.of fun a c => b a (ι c)).det ≠ 0 → B ≤ Λ → (∀ a, b a ∈ B) →
      (B : Set (Fin n → E)) ⊆ Submodule.span E (Set.range b) →
      0 < Nat.card (B ⧸ (Submodule.span (𝓞 E) (Set.range b)).comap B.subtype) ∧
      (Nat.card (B ⧸ (Submodule.span (𝓞 E) (Set.range b)).comap B.subtype) : ℝ) ≤
        D ^ j * |((Algebra.norm ℚ (Matrix.of fun a c => b a (ι c)).det : ℚ) : ℝ)|

def NormProd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (m : I.E), ∏ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = |((Algebra.norm ℚ m : ℚ) : ℝ)|

def LowerBd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ c : ℝ, 0 < c ∧ ∀ s : Size.Sub I x, c ≤ Size.size I s

def LowerBdOf : Prop := LatIs → MinorEx → GramLow → IdxBd → NormProd → LowerBd

def SubEx : Prop := ∀ (I : Formalism.MainNotions.S.AutInst), 1 ≤ I.n → ∀ x : I.GA, Nonempty (Size.Sub I x)

def SubExOf : Prop := LatIs → SubEx

def Assembly : Prop := SizeNear → LowerBd → SubEx → PI.LatSizeCont.LatSizeCont

end PI.UnitaryGroupMassFormula.LSC
