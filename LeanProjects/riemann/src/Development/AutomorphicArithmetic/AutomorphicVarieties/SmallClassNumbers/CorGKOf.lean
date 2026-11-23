import Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.ClassNumberThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TopMainZj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.DefiniteNHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

open Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.J UpperTheory.V.Z.J

namespace UpperTheory.V.SmallClassNumbers

theorem corGK_of (hH : UpperTheory.V.Af.HypothesesH') : U3.CorGK :=
  have hK := UpperTheory.V.ZK.lemmaK_litN_alt hH.litN
  have h3 := UpperTheory.V.HV.Core0.automorphyUnramified_of_litN_of_gdEnd hH.litN (UpperTheory.V.Z.Win.Dn.ends0_alt hH).1
  have hC := UpperTheory.V.HV.Core0.cohInp_alt hH.litN hK
  have hE := unlEnd3E (UpperTheory.V.Z.J.linkedUnlE_alt hH)
  U3.corGK (UpperTheory.V.Z.J.propGK_of_numberU3U_of_oneCharU (UpperTheory.GalN.V.Win.N.numberU3U_of_prints hH.toClassicalTheorems)
    (UpperTheory.V.Z.J.oneCharU_of_katoTwoW_rig_admI_automorphy hC Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP (UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH hH)
      (UpperTheory.V.Z.J.rigIUE_alt hC hH (UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH) hE)
      (UpperTheory.V.Z.Win.RR.rigII_a_alt hC hH (UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)) (UpperTheory.V.Z.J.admissible_typeI_even_level_alt hC hH hE) h3))

theorem litN : GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis :=
  have O : UpperTheory.LiteratureTheorems.OpenImageCondition := UpperTheory.LiteratureTheorems.OpenImageCondition.mk UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  ⟨UpperTheory.One.Join.local_inputs_from_literature O, UpperTheory.One.Join.automorphic_inputs_from_literature O UpperTheory.BaseChangeIdentities.baseChangeN UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter,
    UpperTheory.LiteratureTheorems.galois_cohomology_from_literature O, UpperTheory.One.Join.cm_abelian_inputs_from_literature O⟩

theorem corGK : U3.CorGK := corGK_of (UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt litN UpperTheory.V.Z.Tf.SR.descWeak)

theorem bound : Bound := bound_of corGK

end UpperTheory.V.SmallClassNumbers
