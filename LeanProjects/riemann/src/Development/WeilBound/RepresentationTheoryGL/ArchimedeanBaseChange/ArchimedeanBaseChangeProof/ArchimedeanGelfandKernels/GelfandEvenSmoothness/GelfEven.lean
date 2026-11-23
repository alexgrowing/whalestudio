import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.GelfandEvenSmoothness.IntSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Mult

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def KerComp : Prop := Hyp → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ)
  (k k' k'' : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsBump g' T' → IsKer μ E w g k → IsKer μ E w' g' k' →
    IsKer μ E (w ++ w') (bconv g g') k'' → ∀ y ∈ GLs n, conv μ E k k' y = k'' y

def CoshReal : Prop := ∀ (g : ℝ → ℝ) (T : ℝ) (c : ℝ), IsBump g T → conj (coshT g c) = coshT g c

def GelfEven : Prop := ∀ (n : ℕ) (ψ : Fin n → ℂ), GlobalTheory.Dec.gelfVal (-ψ) 2 = GlobalTheory.Dec.gelfVal ψ 2

end PositivityTheory.RgBcC.Mult
