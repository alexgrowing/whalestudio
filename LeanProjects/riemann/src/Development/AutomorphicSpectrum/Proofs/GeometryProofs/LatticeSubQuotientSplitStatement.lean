import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSubQuotientSplit
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sub_quotient_split : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g s : ℕ) (W V : Submodule Ω E) (W' : Submodule Ω (E ⧸ V)), V ≤ W → L.IsVBOn T g W → (L.map V.mkQ).IsVBOn T s W' → (L.inter V).IsVBOn T (Module.finrank Ω V) V ∧ ∀ p ∈ T, ∃ Q : Submodule (regAt ξ p) E, Disjoint Q (L.inter V p) ∧ Q ⊔ L.inter V p = L p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map | exact GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map | (intros; apply GlobalTheory.CompanionTheory.Ar.inter_isVBOn_of_map <;> assumption)
