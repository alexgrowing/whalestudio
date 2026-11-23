import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions

structure RowsAllN : Prop where
  bloch_kato_dropping_admitted : ∀ D : D7, LocalSituation.Conclusion5 D
  bloch_kato_rank_admitted : ∀ D : D7, LocalSituation.adm5 D
  euler_characteristic_admitted : ∀ D : D7, LocalSituation.adm6 D
  bloch_kato_exactness_admitted : ∀ D : D7, LocalSituation.adm7 D
  tate_duality_admitted : ∀ D : D7, LocalSituation.adm8 D
  selmer_control_admitted : ∀ D : D7, RamifiedCoefficientChains.adm11 D
  automorphic_lift_admitted : ∀ D : D7, RamifiedCoefficientChains.adm12 D
  hecke_eigenvalue_admitted : ∀ D : D7, RamifiedCoefficientChains.adm13 D
  frobenius_semilinearity_admitted : ∀ D : D7, RamifiedCoefficientChains.adm15 D
  crystalline_dimension_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm8 D
  dimension_formula_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm9 D
  galois_invariants_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm10 D
  dual_rank_formula_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm15 D
  period_ring_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm16 D
  congruence_prime_admitted : ∀ D : D7, ElementDenominator.adm7 D
  local_factor_bound_admitted : ∀ D : D7, ElementDenominator.adm8 D
  ramification_bound_admitted : ∀ D : D7, ElementDenominator.adm11 D
  residual_irreducibility_admitted : ∀ D : D7, ElementDenominator.adm12 D
  wach_filtration_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm22 D HW F
  wach_lattice_duality_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm23 D HW F
  lattice_saturation_admitted : ∀ D : D7, tableLineDegreeTwo.adm19 D
  fontaine_comparison_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), tableLineDegreeTwo.adm20 D HW F
  hecke_module_freeness_admitted : ∀ D : D7, tableLineDegreeTwo.adm22 D
  delta_invariant_admitted : ∀ D : D7, WachCoordinates.adm14 D
  fontaine_congruence_admitted : ∀ D : D7, PairedCharacterCondition.FontaineAtPlacesOverL (D := D)
  fontaine_local_admitted : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i
  colength_bound_admitted : ∀ D : D7, LocalTheoryWindows.ArchimedeanSignatureMatching D
  lifting_generators_admitted : ∀ D : D7, LocalTheoryWindows.adm5 D
  unramified_length_admitted : ∀ (D : D7) (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc
  crysOn : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F
  litFont : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.LitFont D HW F
  crysIffWD : ∀ D : D7, CrysIffWD D.nd D.naut
  potCrysIffWD : ∀ D : D7, PotCrysIffWD D.nd D.naut

end Formalism.MainNotions.N

end
