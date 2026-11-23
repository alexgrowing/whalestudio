import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_isLocallySurjective : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q),
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from
      (Arrow.mk f).augmentedCechNerve.hom)) := by
  intro R _ P Q f hf
  exact GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R f (fun U y => ⟨Presheaf.imageSieve f y, hf.imageSieve_mem y, fun V g hg => hg⟩)

end GlobalTheory.EtC
