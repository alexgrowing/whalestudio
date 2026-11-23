import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.GaloisTheoremWithGenerator
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.TheoremFiveArbitraryGroup
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.GaloisThirdWithGenerator

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

namespace Formalism.RepresentationBoundsCohomology.SF

theorem sf_steps : AllSplitF ∧ SplitAllF ∧ StatRealF ∧ StatReal2F ∧ StatRealWAF ∧ StatRealAll1F ∧ StatRealAll2F ∧
    StatRealAllWAF :=
  ⟨realization_all_forms_holds, split_all_second_form, realization_basic_form, realization_second_form, realization_weight_form, realization_all_first_form, realization_all_second_form, realization_all_weight_form⟩

theorem sf_top : GaloisTheoremPrimitiveData ∧ GaloisTheoremWithExtension := ⟨galois_theorem_primitive_data, galois_theorem_with_extension⟩

theorem sf_gen : StatGen ∧ StatCycBc ∧ GaloisTheoremWithGenerator := ⟨gen, cycBc, galois_theorem_with_generator⟩

theorem sf_abs : SplittingTheoremArbitraryGroup := theorem_five_arbitrary_group

theorem galois_theorem_third_forms : GaloisTheoremThirdForm ∧ GaloisThirdWithExtension ∧ GaloisThirdWithGenerator := ⟨galois_theorem_third_form, galois_third_with_extension, galois_third_with_generator⟩

end Formalism.RepresentationBoundsCohomology.SF
