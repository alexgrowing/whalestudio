import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeRankOneEtaleSheafEquivLocallyConstantStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bij_of_subsingleton_pair {A B : Type*} [Subsingleton A] [Subsingleton B] (_b₀ : B) (a₀ : A) (φ : A → B) :
    Function.Bijective φ :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨a₀, Subsingleton.elim _ _⟩⟩

theorem eqv_of_gen_lc : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g →
    ∀ (U V : Scheme.{0}) (s : U ⟶ S) (f : V ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj V) F →
    Function.Bijective (fun φ : LocallyConstant U R ↦ φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  intro R _ F S g hg U V s f hU hV hb n
  obtain ⟨hneg, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  obtain ⟨eL, -, hE⟩ := GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant R F S g hg
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := hneg (sch.obj U) n hn
    have := hneg (sch.obj V) n hn
    exact bij_of_subsingleton_pair 0 0 _
  · have key : (fun x ↦ pull R (sch.map f) F 0 x) =
        (fun x ↦ e V (eL V (f ≫ s) (LocallyConstant.comap f.base.hom ((eL U s).symm ((e U).symm x))))) := by
      funext x
      conv_lhs => rw [← (e U).apply_symm_apply x, ← (eL U s).apply_symm_apply ((e U).symm x)]
      rw [he, hE]
    change Function.Bijective (fun x ↦ pull R (sch.map f) F 0 x)
    rw [key]
    exact (e V).bijective.comp ((eL V (f ≫ s)).bijective.comp
      (hb.comp ((eL U s).symm.bijective.comp (e U).symm.bijective)))
  · have := hU n hn
    have := hV n hn
    exact bij_of_subsingleton_pair 0 0 _

end GlobalTheory.EtC
