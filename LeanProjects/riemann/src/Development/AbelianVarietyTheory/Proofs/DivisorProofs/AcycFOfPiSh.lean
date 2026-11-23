import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquivStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acycF_of_pi_sh : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type)
    [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) →
    AcycF R (sp B) F := by
  intro R _ F ι _ T _ B _ ⟨e⟩ hT n hn
  obtain ⟨hc⟩ := GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv ι T B e
  have hbij := GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective R F (Spec (CommRingCat.of B)) ι (fun i => Spec (CommRingCat.of (T i)))
    (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))) hc n
  have hsub : ∀ i, Subsingleton (H R (sch.obj (Spec (CommRingCat.of (T i)))) F n) :=
    fun i => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf R (T i) (hT i) F n hn
  refine ⟨fun x y => hbij.1 ?_⟩
  funext i
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
