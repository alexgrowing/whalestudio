import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem eigencomponents_scalars : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) :=
  @PositivityTheory.HtPt.Rb.proj_props

end GlobalTheory.CompanionTheory.Ar.GR
