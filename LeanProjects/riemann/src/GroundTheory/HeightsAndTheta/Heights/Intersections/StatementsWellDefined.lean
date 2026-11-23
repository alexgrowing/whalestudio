import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def AddAt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A C : HermLine ι),
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm C →
    I W (n + 1) (Fin.snoc L (A.tensor C)) = I W (n + 1) (Fin.snoc L A) + I W (n + 1) (Fin.snoc L C)

def RPositionAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A C B : HermLine ι) (s : MRing ι),
    AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSmoothHerm C → IsSmoothHerm B → IsSectionOn P B s →
    recR I P (Fin.snoc L (A.tensor C)) B s = recR I P (Fin.snoc L A) B s + recR I P (Fin.snoc L C) B s

def WellDefined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin (n + 1) → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    HasRAt I n → AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

end

end GroundTheory.Heights₂.Heights.Inter
