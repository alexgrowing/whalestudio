import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.affFin_of :
    AffFinProj := by
  intro R _ Y f hf s
  haveI : GlobalTheory.FiniteSubsetsInAffineOpens Y := GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver hf
  obtain ⟨U, hU, hsub⟩ :=
    GlobalTheory.FiniteSubsetsInAffineOpens.exists_isAffineOpen (X := Y) (s : Set Y) s.finite_toSet
  exact ⟨U, hU, fun x hx => hsub (Finset.mem_coe.mpr hx)⟩
