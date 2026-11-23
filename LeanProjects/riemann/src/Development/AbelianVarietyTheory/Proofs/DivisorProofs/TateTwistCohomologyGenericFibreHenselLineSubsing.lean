import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjOfStrictHenselisationPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianDirectedUnionSubalgebrasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicGenericFibreQuotientStrictHenselisationNoTorsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.LocAcycDegOne

open scoped TensorProduct

theorem unitsL : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA
  obtain ⟨O, _, _, _, _, _, _, π, hπ, hO⟩ := GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt T A hSH hA
  exact GlobalTheory.T.henselian_directed_union_subalgebras q T hT hq O hO A π hπ

theorem picL : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA
  obtain ⟨O, _, _, _, _, _, _, π, hπ, hO⟩ := GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt T A hSH hA
  exact GlobalTheory.T.pic_generic_fibre_quotient_strictHenselisation_no_torsion_alt q T hT hq O hO A π hπ

theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (T B : Type) [CommRing T] [Nontrivial T] [CommRing B] [Algebra T B] (hT : AIC T) :
    ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  have hcyc : (Polynomial.cyclotomic q T).Monic := Polynomial.cyclotomic.monic q T
  have hdeg : 0 < (Polynomial.cyclotomic q T).natDegree := by
    rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨ζ, hζ⟩ := hT _ hcyc hdeg
  refine ⟨algebraMap T B ζ, ?_⟩
  have h0 := congrArg (algebraMap T B) hζ
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, Polynomial.hom_eval₂, map_zero] at h0
  rw [Polynomial.aeval_def, algebraMap_int_eq]
  rwa [show (algebraMap T B).comp (Int.castRingHom T) = Int.castRingHom B from RingHom.ext_int _ _] at h0

theorem tateTwistCohomology_genericFibre_henselLine_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ i : ℤ, Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 i) := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA i
  have hqB : IsUnit (q : TensorProduct T (FractionRing T) A) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  have hz := exists_cyclotomic_root q T (TensorProduct T (FractionRing T) A) hT
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (TensorProduct T (FractionRing T) A) hqB hz 1 i 1
  have h1 : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 1) :=
    GlobalTheory.T.kummer_etale_vanishing q _ hqB (fun u => (unitsL q T hT hq A hSH hA u).imp fun _ h => h.symm) (picL q T hT hq A hSH hA)
  refine ⟨fun x y => e.injective ?_⟩
  exact Subsingleton.elim _ _

end GlobalTheory.LocAcycDegOne
