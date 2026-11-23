import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBoundAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

def hf (I : Formalism.MainNotions.S.AutInst) (w z : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J w z

def pairM (I : Formalism.MainNotions.S.AutInst) {k : ℕ} (b' u : Fin k → Fin I.n → I.E) : Matrix (Fin k) (Fin k) I.E :=
  Matrix.of fun a c => hf I (b' a) (u c)

def PerpKer (I : Formalism.MainNotions.S.AutInst) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (w : Fin I.n → I.E) : Prop :=
  ∀ z, δ *ᵥ z = 0 → hf I w z = 0

def perpE (I : Formalism.MainNotions.S.AutInst) (δ : Matrix (Fin I.n) (Fin I.n) I.E) : Submodule I.E (Fin I.n → I.E) where
  carrier := {w | PerpKer I δ w}
  add_mem' := by
    intro a b ha hb z hz
    have h1 := ha z hz
    have h2 := hb z hz
    simp only [hf, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' := by
    intro z _
    simp [hf, Formalism.UG.hform]
  smul_mem' := by
    intro c a ha z hz
    have h1 := ha z hz
    simp only [hf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc] at h1 ⊢
    simp only [← Finset.mul_sum] at h1 ⊢
    rw [h1, mul_zero]

def imSub (I : Formalism.MainNotions.S.AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (δ : Matrix (Fin I.n) (Fin I.n) I.E) :
    Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Λ.map ((Matrix.mulVecLin δ).restrictScalars (𝓞 I.E))

def perpSub (I : Formalism.MainNotions.S.AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (δ : Matrix (Fin I.n) (Fin I.n) I.E) :
    Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Λ ⊓ (perpE I δ).restrictScalars (𝓞 I.E)

def idx (I : Formalism.MainNotions.S.AutInst) (B : Submodule (𝓞 I.E) (Fin I.n → I.E)) {k : ℕ} (b : Fin k → Fin I.n → I.E) : ℕ :=
  Nat.card (B ⧸ (Submodule.span (𝓞 I.E) (Set.range b)).comap B.subtype)

def LatIsG : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ Λ : Submodule (𝓞 I.E) (Fin I.n → I.E), Λ.FG ∧
    Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤ ∧ PI.LatCountG.latSet I x = (Λ : Set (Fin I.n → I.E))

def DualIncl : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (y : I.GA) (u : Fin I.n → I.E),
    (∀ w ∈ PI.LatCountG.latSet I y, hf I w u ∈ (algebraMap (𝓞 I.E) I.E).range) → u ∈ PI.LatCountG.latSet I y

def Choose : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (y : I.GA) (δ : Matrix (Fin I.n) (Fin I.n) I.E), δ ≠ 0 →
    ∃ (k : ℕ) (u b' : Fin k → Fin I.n → I.E), 1 ≤ k ∧
      (∀ c, u c ∈ PI.LatCountG.latSet I y) ∧ LinearIndependent I.E (fun c => δ *ᵥ u c) ∧
      (∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c)) ∧
      (∀ a, b' a ∈ PI.LatCountG.latSet I y) ∧ LinearIndependent I.E b' ∧ (∀ a, PerpKer I δ (b' a)) ∧
      (∀ w, PerpKer I δ w → w ∈ Submodule.span I.E (Set.range b'))

def ArchIneq : Prop :=
  ∀ (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (C D : Matrix (Fin n) (Fin k) ℂ) (κ : ℝ), 0 ≤ κ →
    (∀ w : Fin n → ℂ, PI.UnitaryGroupMassFormula.LSC.nsq (A *ᵥ w) ≤ κ * PI.UnitaryGroupMassFormula.LSC.nsq w) →
    (∀ z : Fin n → ℂ, Dᴴ *ᵥ z = 0 → A *ᵥ z = 0) →
    (((A * C)ᴴ * (A * C)).det).re * ((Dᴴ * D).det).re ≤ κ ^ k * ‖(Dᴴ * C).det‖ ^ 2

def ArchPlace : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ)
    (u b' : Fin k → Fin I.n → I.E) (v : InfinitePlace I.F),
    LinearIndependent I.E (fun c => δ *ᵥ u c) →
    (∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c)) →
    LinearIndependent I.E b' → (∀ a, PerpKer I δ (b' a)) →
    ((PI.LatCountG.gramV I x v (fun c => δ *ᵥ u c)).det).re * ((PI.LatCountG.gramV I y v b').det).re ≤
      hsN (amat I x y v δ) ^ (2 * k) * ‖I.φ v (pairM I b' u).det‖ ^ 2

def IndexIneq : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Λ.FG →
    Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤ →
    (∀ u, (∀ w ∈ Λ, hf I w u ∈ (algebraMap (𝓞 I.E) I.E).range) → u ∈ Λ) →
    ∀ (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ) (u b' : Fin k → Fin I.n → I.E),
      (∀ c, u c ∈ Λ) → LinearIndependent I.E (fun c => δ *ᵥ u c) →
      (∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c)) →
      (∀ a, b' a ∈ Λ) → LinearIndependent I.E b' → (∀ a, PerpKer I δ (b' a)) →
      (∀ w, PerpKer I δ w → w ∈ Submodule.span I.E (Set.range b')) →
      idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) ≠ 0 → idx I (perpSub I Λ δ) b' ≠ 0 →
      |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)| ≤
        (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)

def SepOf : Prop :=
  LatIsG → DualIncl → Choose → ArchPlace → IndexIneq → PI.UnitaryGroupMassFormula.LSC.NormProd → PI.UnitaryGroupMassFormula.LSC.DetMono → CardPl → Sep

def ArchPlaceOf : Prop := ArchIneq → ArchPlace

end PI.UnitaryGroupMassFormula.LCG
