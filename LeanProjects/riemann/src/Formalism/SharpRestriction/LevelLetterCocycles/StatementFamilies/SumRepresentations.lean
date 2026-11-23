import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.SumRepresentations

open Formalism.BasicNotions Formalism.MainNotions

def ConclusionF1 {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i)

def ConclusionF2 {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i)

def AdmAF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AdmAt (Fm.D x i)

def AdmF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, admitted (Fm.D x i)

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := (AdmAF Fm → ConclusionF1 Fm) ∧ (AdmF Fm → ConclusionF2 Fm)

end Formalism.MainNotions.SumRepresentations

end
