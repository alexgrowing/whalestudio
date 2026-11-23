import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHenselStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSectionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sh_eqv_tw : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  intro q i A B _ _ φ hA hB hq
  obtain ⟨hAl, _⟩ := hA
  obtain ⟨hBl, _⟩ := hB
  obtain ⟨ζ⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A ⟨hAl, ‹_›⟩ hq
  let S : Scheme.{0} := Spec (CommRingCat.of A)
  let ζS : Prim q Γ(S, ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ζ
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζS
  have hac : ∀ (C : Type) [CommRing C], SH C → AcycF (ZMod q) (sch.obj (Spec (CommRingCat.of C))) (tw q i) :=
    fun C _ hC n hn => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) C hC (tw q i) n hn
  refine GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) S (twGen i ζS) hgen S (Spec (CommRingCat.of B)) (𝟙 S)
    (Spec.map (CommRingCat.ofHom φ)) (hac A ⟨hAl, ‹_›⟩) (hac B ⟨hBl, ‹_›⟩) ?_
  have cA := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) A
  have cB := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) B
  have hcomp : (fun φ' : LocallyConstant S (ZMod q) => φ'.comap (Spec.map (CommRingCat.ofHom φ)).base.hom) ∘
      (fun c : ZMod q => LocallyConstant.const S c) = fun c => LocallyConstant.const _ c := by
    funext c; ext x; rfl
  refine (Function.Bijective.of_comp_iff _ cA).1 ?_
  rw [hcomp]
  exact cB
end GlobalTheory.EtC
