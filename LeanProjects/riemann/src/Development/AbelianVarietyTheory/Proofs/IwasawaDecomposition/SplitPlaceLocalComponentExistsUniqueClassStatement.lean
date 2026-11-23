import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L), ∃ σ, IsLocS π.S s σ ∧ ∀ (π' : NG.AutRep L n) (s' : SplitPlace L) (h : s'.w = s.w) σ', π.Iso π' → IsLocS π'.S s' σ' → HEq σ'.cl σ.cl := by
  first | exact @GlobalTheory.LocCompSplit.main | exact GlobalTheory.LocCompSplit.main | (intros; apply GlobalTheory.LocCompSplit.main <;> assumption)
