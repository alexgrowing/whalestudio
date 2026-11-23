import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeTermsSheafExtSubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.AcycRes

theorem coneBij {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J)
    (h : ∀ m, Subsingleton (CohomologyClass K (mappingCone f) m)) (n : ℤ) : Function.Bijective (cpush K f n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f m
  obtain ⟨h1, -, -⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f (m + 1)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h3 x).1 hx
    rw [(h m).elim y 0, map_zero]
  · intro y
    exact (h1 y).1 ((h (m + 1)).elim _ _)

theorem subOfIso {R : Type} [CommRing R] {A B : Shv R} (e : A ≅ B) (M : Cx R) (n : ℤ)
    (h : Subsingleton (CohomologyClass (sgl B) M n)) : Subsingleton (CohomologyClass (sgl A) M n) := by
  obtain ⟨hid, hcomp, -, -, -⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have key : ∀ z, cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.hom) M n
      (cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.inv) M n z) = z := by
    intro z
    rw [← hcomp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
    exact (hid _ _ _ z).1
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y, h.elim (cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.inv) M n x)]

theorem discFree {R : Type} [CommRing R] (P : PSh) (X : Shv R) (i : ℤ) (h : Subsingleton (H R (disc.obj P) X i)) :
    Subsingleton (CohomologyClass (sgl ((free R).obj P)) (res R X) i) := by
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨hid, hcomp, -, -, hhtpy⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have key : ∀ z, cpull (e P).hom (res R X) i (cpull (e P).inv (res R X) i z) = z := by
    intro z
    rw [← hcomp, (hhtpy _ _ ⟨(e P).homotopyHomInvId⟩ (res R X) i).1]
    exact (hid _ _ _ z).1
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y, h.elim (cpull (e P).inv (res R X) i x)]

end GlobalTheory.EtC.AcycRes

open GlobalTheory.EtC.AcycRes in

theorem GlobalTheory.EtC.acycRes_computes : ∀ (R : Type) [CommRing R] (F : Shv R) (C : Cx R) [C.IsStrictlyGE 0] (ε : sgl F ⟶ C) [QuasiIso ε] (u : C ⟶ res R F), ε ≫ u = resAug F → (∀ (t : ℤ) (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) (C.X t) n)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains R).obj E) u n) := by
  intro R _ F C _ ε _ u hu hC E n
  obtain ⟨-, hinj, hge, hqa, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  have : QuasiIso (ε ≫ u) := by rw [hu]; exact hqa
  have : QuasiIso u := quasiIso_of_comp_left ε u
  have : ((chains R).obj E).IsStrictlyLE 0 := (GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R).1 E
  have : (mappingCone u).IsStrictlyGE (-1) := isStrictlyGE_mappingCone u 0 0 (-1)
  apply coneBij
  intro m
  apply GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero R _ _ _ m
  intro p k hp
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
  apply subOfIso (chainsXIso R E q)
  apply GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow R _ _ (-1) (GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso R u)
  intro t i hi
  apply GlobalTheory.T.mappingCone_terms_sheafExt_subsingleton R _ u hinj _ t i hi
  intro t' i' hi'
  exact discFree _ _ _ (hC t' _ i' hi')
