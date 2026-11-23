import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) :
    Fin (a + 1) → Submodule ℂ (Fin I.n → ℂ) :=
  fun i => Submodule.span ℂ ((fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) '' (S i : Set _))

def IsSatFlag (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  S 0 = ⊥ ∧ Monotone S ∧ (∀ i : Fin a, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i) ∧
    (∀ i, ∀ y, y ∈ S i ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (S i : Set (Fin I.n → I.E))) ∧
    ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def IsGaugeAll (I : AutInst) (c : InfinitePlace I.F → ℝ) : Prop := ∀ v, IsGauge (I.ε v) (c v)

def cIw (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2)) * (volU p * volU q) /
    ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i))

def rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ((M : ℝ) - 1 / 2)) * Formalism.HermitianLatticesTheory.lValEta E M

end GlobalTheory.FlagMeas
