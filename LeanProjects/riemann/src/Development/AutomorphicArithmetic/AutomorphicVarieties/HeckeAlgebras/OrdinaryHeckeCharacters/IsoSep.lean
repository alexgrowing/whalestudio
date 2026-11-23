import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsoSeparation

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi

theorem UpperTheory.V.Hi.isoSep :
    ∀ {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M]
        {ρ : Representation ℂ H M} {Y : Submodule ℂ M} {σ : SmIrr H}, IsoSum ρ Y σ → ∀ {F : M}, F ∈ Y → F ≠ 0 →
        ∃ p : M →ₗ[ℂ] σ.V, (∀ g, ∀ y ∈ Y, p (ρ g y) = σ.ρ g (p y)) ∧ p F ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.IsoSeparation.isoSep
