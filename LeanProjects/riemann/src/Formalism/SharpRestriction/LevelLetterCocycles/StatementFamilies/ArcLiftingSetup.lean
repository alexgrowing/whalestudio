import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.ArcLiftingSetup

open Formalism.BasicNotions

abbrev LayF (Dm : Formalism.MainNotions.DFamP) : Type 1 :=
  ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52) (x : ℝ) (i : (Dm ε h0 h1).Ix x),
    Σ HW : Formalism.BasicNotions.HWOf ((Dm ε h0 h1).D x i).loc,
      Σ F : Formalism.BasicNotions.FonOf ((Dm ε h0 h1).D x i).loc ((Dm ε h0 h1).D x i).locA HW,
        Formalism.BasicNotions.CmpOf ((Dm ε h0 h1).D x i).loc ((Dm ε h0 h1).D x i).locA HW F

def OrbitValuationBound (Dm : Formalism.MainNotions.DFamP) (L : LayF Dm) : Prop :=
  ∃ C₀ : ℝ, ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), ∃ x0 : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ x : ℝ, x0 ≤ x →
    ∀ i : (Dm ε h0 h1).Ix x, aux₃ ((Dm ε h0 h1).D x i) (L ε h0 h1 x i).1 (L ε h0 h1 x i).2.1 C

def AdmF (Dm : Formalism.MainNotions.DFamP) (L : LayF Dm) : Prop :=
  ∃ CR CA CB CK Ckap : ℝ, ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    ∀ i : (Dm ε h0 h1).Ix x,
      admitted ((Dm ε h0 h1).D x i) (L ε h0 h1 x i).1 (L ε h0 h1 x i).2.1 (L ε h0 h1 x i).2.2 CR CA CB CK Ckap

def KudlaFamilyStatement (Dm : Formalism.MainNotions.DFamP) (L : LayF Dm) : Prop := AdmF Dm L → OrbitValuationBound Dm L

end Formalism.MainNotions.ArcLiftingSetup

end
