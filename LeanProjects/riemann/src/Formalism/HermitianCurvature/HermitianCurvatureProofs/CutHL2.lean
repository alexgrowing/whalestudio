import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section defs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Hyp (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ IsOpen Dm ∧ Dm ⊆ domJ k r j hj z z' ∧ RulesOn k r j hj z z' Dm Φ ∧
    Z.det ≠ 0 ∧ τ ≠ 0 ∧ γ ∈ B.GV k (r - (j + 1)) ∧ x0 k r j hj Z τ γ ∈ Dm

def Eq1 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) + levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) +
      τ • PBP.dz (fun τ' => D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      τ • D.vLet k r z z' j (by omega) (true, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq2 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (true, Y) 1 Φ (x0 k r j hj Z τ γ) =
    τ⁻¹ • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ)

def Eq3 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 0 Φ (x0 k r j hj Z τ γ) =
    ((Y : ℂ) - levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ) -
      conj τ • PBP.dzb (fun τ' => D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
      conj τ • D.vLet k r z z' j (by omega) (false, Y) 1 Φ (x0 k r j hj Z τ γ)

def Eq4 (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Q.Mx k r → E)
    (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ) (Y : ℝ) : Prop :=
  D.vLet k r z z' (j + 1) hj (false, Y) 1 Φ (x0 k r j hj Z τ γ) =
    (conj τ)⁻¹ • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ)

end defs

def Comp1 : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq2 k r j hj z z' Φ Z γ τ Y ∧ Eq4 k r j hj z z' Φ Z γ τ Y

def PlusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def PlusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq1 k r j hj z z' Φ Z γ τ Y

def MinusPos : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), 1 ≤ j → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

def MinusZero : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ)
    (γ : B.Mat k (r - (j + 1))) (τ : ℂ), j = 0 → Hyp k r j hj z z' Dm Φ Z γ τ →
    ∀ Y : ℝ, Eq3 k r j hj z z' Φ Z γ τ Y

theorem headLetter_of (h1 : Comp1) (hPP : PlusPos) (hPZ : PlusZero) (hMP : MinusPos) (hMZ : MinusZero) :
    LevelPointCoordinates.HeadLetter := by
  intro k r j hj z z' E _ _ Dm Φ hz hz' hD hDs hR Z γ τ hZ hτ hγ hx Y
  have hH : Hyp k r j hj z z' Dm Φ Z γ τ := ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩
  obtain ⟨c2, c4⟩ := h1 k r j hj z z' E Dm Φ Z γ τ hH Y
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · exact ⟨hPZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c2, hMZ k r j hj z z' E Dm Φ Z γ τ h0 hH Y, c4⟩
  · exact ⟨hPP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c2, hMP k r j hj z z' E Dm Φ Z γ τ hpos hH Y, c4⟩

def NormalFormsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.xi0 (x0 k r j hj Z τ γ) a p = if p.val < j + 1 then C3.Zb j 1 Z τ a.val p.val else 0) ∧
    (∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < j + 1 →
      PBG.y0 (x0 k r j hj Z τ γ) a p =
        if r + k < p.val ∧ 2 * r + k - p.val < j + 1 then star (C3.Zb j 1 Z τ a.val (2 * r + k - p.val)) else 0)

def LeadingMinorsAtBasePoint : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det ∧
      Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j + 1, by omega⟩ = Z.det * τ

def LeftActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (τ * Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩) • Ψ (x0 k r j hj Z τ γ)

def TorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      τ • PBP.dz (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ

def ConjugateActionRuleAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), 1 ≤ j → inWb k r z → IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    (∀ a : Fin j → ℂ, Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ)) →
    ∀ b : Fin j, Q.EH k r (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      (conj τ * conj (Z⁻¹ b ⟨j - 1, by have := b.isLt; omega⟩)) • Ψ (x0 k r j hj Z τ γ)

def ConjugateTorusDirectionAtBasePoint : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))), IsOpen Dm → Q.SmoothLev k r 0 Dm Ψ → Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
    Q.EH k r (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) Ψ (x0 k r j hj Z τ γ) =
      -(conj τ • PBP.dzb (fun τ' => Ψ (x0 k r j hj Z τ' γ)) τ)

def FrozenX : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' u : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ' γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u ∧
      Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩) * C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u =
        C3.AAx k r Eu (PBG.xi0 (x0 k r j hj Z τ γ)) j (by omega) u * Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)

def FrozenV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (k r j : ℕ) (hj : j + 1 ≤ r)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' ℓ : ℂ)
    (γ : B.Mat k (r - (j + 1))), GlRel Eu → Z.det ≠ 0 → τ ≠ 0 → τ' ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ' γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ ∧
      Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩) * C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ =
        C3.AAv k r Eu (PBG.y0 (x0 k r j hj Z τ γ)) j (by omega) ℓ * Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)

def Comp1OfParts : Prop := NormalFormsAtBasePoint → Comp1

def PlusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → LeftActionRuleAtBasePoint → TorusDirectionAtBasePoint → FrozenX → PlusPos

def PlusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → TorusDirectionAtBasePoint → PlusZero

def MinusPosOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateActionRuleAtBasePoint → ConjugateTorusDirectionAtBasePoint → FrozenV → MinusPos

def MinusZeroOfParts : Prop := NormalFormsAtBasePoint → LeadingMinorsAtBasePoint → ConjugateTorusDirectionAtBasePoint → MinusZero

theorem headLetter_of_leaves (hNf : NormalFormsAtBasePoint) (hDm : LeadingMinorsAtBasePoint) (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint)
    (hST : ConjugateTorusDirectionAtBasePoint) (hFX : FrozenX) (hFV : FrozenV) (h1 : Comp1OfParts) (hPP : PlusPosOfParts)
    (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of (h1 hNf) (hPP hNf hDm hL hT hFX) (hPZ hNf hDm hT) (hMP hNf hDm hSL hST hFV) (hMZ hNf hDm hST)

end Formalism.FourierDecayAlt.P.CutHL
