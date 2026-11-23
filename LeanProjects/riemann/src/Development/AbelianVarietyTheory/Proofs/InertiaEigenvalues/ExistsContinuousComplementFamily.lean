import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem exists_continuous_complementFamily {D : D7} (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) :
    ∃ ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ π, Continuous
        (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) ∧
      ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) (ρ π) := by
  have key : ∀ π : D.nd.X i, ∃ ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
      (π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) ρ) := by
    intro π
    by_cases hπ : π ∈ D.nd.Z i
    · obtain ⟨ρ, hρ⟩ := h i π hπ (r π) (hr π)
      exact ⟨ρ, hρ.cont, fun _ => hρ⟩
    · exact ⟨1, continuous_const, fun h' => absurd h' hπ⟩
  choose ρ h1 h2 using key
  exact ⟨ρ, h1, h2⟩

theorem exists_ptFam : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    (∀ i, ∃ r, GoodR D.nd i r) → ∃ r ρ, PtFam D r ρ := by
  intro hC D hG hr
  choose r hr using hr
  choose ρ h1 h2 using fun i =>
    exists_continuous_complementFamily (GlobalTheory.BlockComplement.complement_at hC D hG) i (r i) (hr i)
  exact ⟨r, ρ, hr, h1, h2⟩

end GlobalTheory.PtCore
