import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialIsotypicLatticeOfParts
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestWeightVectorFindim
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MultidegreePartFinitelyGenerated
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralGeneratorsPreserveLattice

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem integral_formula_lattice_holds : AdmissibleDVRIntegralFormLatticesStable := by
  intro p n' O _ _ _ S0 hG
  have hV : ValuationProperties p O := valuation_properties_hold hG.prime S0
  have hchar := dvr_fraction_field_char_zero hG.prime S0
  exact ⟨hchar, fun n ι _ LL => ⟨fun S => integral_formula_stability_holds hG.prime hV n ι LL S,
    fun S => char_zero_stability_of_closure hG.prime hchar (fock_lattice_closure_holds hV) n ι LL S, fock_lattice_finite_spanning_holds hG.prime S0 hV n ι⟩⟩

theorem integral_polynomials_enveloping_stable (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S0 : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι) :
    PolUZStable LL S (IntPol O (ι × Fin n)) ∧
      ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
        InBB (O := O) p F → InBB (O := O) p (u F) :=
  ((integral_formula_lattice_holds p n' O S0 hG).2 n ι LL).1 S

theorem polynomial_isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D :=
  polynomial_isotypic_lattice_of_parts D (complete_reducibility_of_semisimple D h2) contravariant_orthogonality_holds highest_weight_dominant_holds (subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2)) polynomial_representation_holds integral_formula_lattice_holds h13

end Formalism.MainNotions.G.GLWeightTheory
