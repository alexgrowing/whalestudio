import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicallyIndependentLeTrdeg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraically_independent_le_trdeg : ∀ {k K Ω : Type} [Field k] [Field K] [Field Ω] (r : k →+* K) (σ ι : K →+* Ω), σ.comp r = ι.comp r →
    ∀ {J : Type} [Fintype J] (e : J → Ω), (∀ j, e j ∈ Subfield.closure (Set.range ι ∪ Set.range σ)) →
    (letI : Algebra K Ω := ι.toAlgebra; AlgebraicIndependent K e) →
    (Fintype.card J : Cardinal) ≤ (letI : Algebra k K := r.toAlgebra; Algebra.trdeg k K) := by
  first | exact @GlobalTheory.card_algebraicIndependent_compositum_le_trdeg | exact GlobalTheory.card_algebraicIndependent_compositum_le_trdeg | (intros; apply GlobalTheory.card_algebraicIndependent_compositum_le_trdeg <;> assumption)
