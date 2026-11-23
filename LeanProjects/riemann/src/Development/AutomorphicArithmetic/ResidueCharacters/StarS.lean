import Development.AutomorphicArithmetic.ResidueCharacters.RowAtOfSetup
import Development.AutomorphicArithmetic.ResidueCharacters.RowGlue

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem UpperTheory.N.starS (hP : Hypotheses₂) : UpperTheory.N.StarSF := by
  obtain ⟨A, B, hA, hB, h⟩ := UpperTheory.N.rowC hP
  exact UpperTheory.N.starSF_of_rowC A B hA hB h
