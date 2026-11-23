import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def IsAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I.n = I₀.n + 2 * ∑ i, j i ∧ (∀ i, Submodule.IsLattice I.E (Λ i)) ∧
    (∀ i k, (T i)ᴴ * I.J * T k = 0 ∧ (T' i)ᴴ * I.J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * I.J * T' k = 0)) ∧
    (∀ i, (T i)ᴴ * I.J * T' i = 1 ∧ (T i)ᴴ * I.J * T₀ = 0 ∧ (T' i)ᴴ * I.J * T₀ = 0) ∧
    T₀ᴴ * I.J * T₀ = I₀.J.map e ∧
    (∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l)) ∧
    ∀ k z, z ∈ S k ↔ ∃ u : ∀ i, Fin (j i) → I.E, (∀ i, u i ∈ Λ i) ∧ (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧
      z = ∑ i, T i *ᵥ u i

def latGroup (I : AutInst) (xf : I.Gf) : Set I.Ginf :=
  {g | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset}

def flagGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {g | g ∈ latGroup I xf ∧ ∀ v k, ∀ y ∈ flagAt I S v k, uMat (g v) *ᵥ y ∈ flagAt I S v k}

def leviGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {m | (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ∧
    ∃ g ∈ flagGroup I xf S, ∃ u : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) ∧ g = u * m}

def sizesAt (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (g : I.Ginf) : Fin a → ℝ :=
  fun i => Formalism.HN.sizeQ (bas I) (frm I (g, xf)) (S i.succ) (S i.castSucc)

def slabVol (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ENNReal :=
  covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

section Mean

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

abbrev VecInf : Type := InfinitePlace E → Fin j → ℂ

def latAt (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ ((fun (y : Fin j → E) (w : InfinitePlace E) =>
    (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a)) '' (Λ : Set (Fin j → E)))

def dualAt (L : Submodule ℤ (VecInf E j)) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ {y | ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z}

def latMean (F : Submodule ℤ (VecInf E j) → ENNReal) : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) ((haarGL E j).withDensity fun g => F (latAt E j (Quot.out c).1 g))
      {g | 0 < detNorm E j g}

def IsLatMeasurable (F : Submodule ℤ (VecInf E j) → ENNReal) : Prop :=
  ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable fun g : MatInf E j => F (latAt E j Λ g)

def covAt (L : Submodule ℤ (VecInf E j)) : ℝ := ZLattice.covolume L volume

def gaussV (x : VecInf E j) : ℝ := Real.exp (-Real.pi * ∑ w, ∑ a, ‖x w a‖ ^ 2)

end Mean

end GlobalTheory.FlagBase
