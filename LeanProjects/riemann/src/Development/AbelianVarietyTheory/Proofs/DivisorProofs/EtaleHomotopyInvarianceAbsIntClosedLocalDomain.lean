import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.HtpyLine

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem bijective_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (f : M →+ N) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end GlobalTheory.EtC.HtpyLine

namespace GlobalTheory.EtC.HtpyLine

open Polynomial

theorem exists_cyclotomic_root_of_AIC (q : ℕ) [NeZero q] (T : Type) [CommRing T] [Nontrivial T] (hA : AIC T) :
    ∃ ζ : T, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨a, ha⟩ := hA (cyclotomic q T) (cyclotomic.monic q T)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
  refine ⟨a, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact ha

theorem htpy_AIC : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  intro q _ T _ _ _ hA hq i n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 (sp T) n hn
    haveI := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 (sp (Polynomial T)) n hn
    exact bijective_of_subsingleton _
  · exact GlobalTheory.T.h_zero_pullback_twist_bijective q T (Polynomial T) Polynomial.C hq (exists_cyclotomic_root_of_AIC q T hA) inferInstance
      (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) i
  · haveI hT : Subsingleton (Ht q (sp T) n i) := GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic q T hA hq n i hn
    haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
    have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
    haveI hKt : Subsingleton (Ht q (sp (Polynomial (FractionRing T))) n i) := GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed q (FractionRing T) hqK n i hn
    let e : TensorProduct T (FractionRing T) (Polynomial T) ≃+* Polynomial (FractionRing T) :=
      (polyEquivTensor T (FractionRing T)).symm.toRingEquiv
    haveI hTens : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) (Polynomial T))) n i) :=
      (pull_bijective_of_ringEquiv e (tw q i) n).1.subsingleton
    have hC3 := GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq (Polynomial T) i n
    haveI : Subsingleton (Ht q (sp (Polynomial T)) n i) := hC3.1.subsingleton
    exact bijective_of_subsingleton _

end GlobalTheory.EtC.HtpyLine
