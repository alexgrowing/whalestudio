import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRooStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTwStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictlyHenselianOfIsFieldMonicRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AicAcyc

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : AIC K := by
  intro p hp hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) : IsIso (spMap (e : A →+* B)) := by
  haveI : IsIso (CommRingCat.ofHom (e : A →+* B)) := (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold spMap
  infer_instance

end GlobalTheory.EtC.AicAcyc

namespace GlobalTheory.EtC

open GlobalTheory.EtC.AicAcyc in

theorem b5 : B5 := by
  intro q A _ _ hA hq n i hn
  haveI := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  have hK : SH (FractionRing A) :=
    GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots (FractionRing A) (Field.toIsField _) (aic_of_isAlgClosed _)
  have hE := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have heqv : Eqv (ZMod q) (spMap (algebraMap A (FractionRing A))) (tw q i) := by
    refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A A (FractionRing A)
      (Algebra.ofId A (FractionRing A)) ?_
    intro O _ _ hO hOind
    obtain ⟨hfield, haic⟩ := GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian A O hA hO hOind
    have hSH : SH (O ⊗[A] FractionRing A) := GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots _ hfield haic
    have hqO : IsUnit (q : O) := by
      simpa using hq.map (algebraMap A O)
    let e := Algebra.TensorProduct.rid A A O
    let j : O →ₐ[A] O ⊗[A] FractionRing A := Algebra.TensorProduct.includeLeft
    have hψ : (Algebra.TensorProduct.map (AlgHom.id A O) (Algebra.ofId A (FractionRing A))) =
        j.comp e.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro o a
      simp [j, e, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hψ]
    have h1 : Eqv (ZMod q) (spMap (j : O →+* O ⊗[A] FractionRing A)) (tw q i) :=
      GlobalTheory.T.eqv_spMap_tw_of_isUnit q i O _ (j : O →+* O ⊗[A] FractionRing A) hO hSH hqO
    have h2 : Eqv (ZMod q) (spMap ((e : O ⊗[A] A ≃+* O) : O ⊗[A] A →+* O)) (tw q i) := by
      haveI := isIso_spMap (e : O ⊗[A] A ≃+* O)
      exact hE.1 _ _ _ inferInstance
    have h3 := (hE.2.1 _ _ _ _ _).1 h1 h2
    rw [← spMap_comp] at h3
    exact h3
  have hacK : AcycF (ZMod q) (sp (FractionRing A)) (tw q i) :=
    fun m hm => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) (FractionRing A) hK (tw q i) m hm
  exact (hE.2.2.2 _ _ _ heqv).1 hacK n hn

end GlobalTheory.EtC

end
