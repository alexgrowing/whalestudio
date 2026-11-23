import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pAtApart :
    JEq → AtApart := by
  intro hJ
  unfold AtApart
  intro E _ _ _ A n p _ S T hc w hw hp
  have key : ∀ (u : Plc E) (hu : IsSplitAt u) (hpu : (p : 𝓞 E) ∉ u.asIdeal)
      (x : GL (Fin n) (u.adicCompletion E)),
      T.sec ((T.at hc u hu hpu).loc x) = UpperTheory.Gal.CertificateRingHomMap.loc hu x := by
    intro u hu hpu x
    apply (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
    intro v
    by_cases hv : (p : 𝓞 E) ∈ v.asIdeal
    · rw [T.sec_p _ v hv, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hu (apart_of_not_mem hpu hv)]
    · exact (T.j_eq _ _).1 (T.j_sec _) v hv
  refine ⟨key w hw hp, ?_⟩
  intro w' hw' hp' hap
  constructor
  · intro x
    show comp w (T.sec ((T.at hc w' hw' hp').loc x)) = 1
    rw [key w' hw' hp' x]
    exact UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw' hap x
  · intro x
    show comp w' (T.sec ((T.at hc w hw hp).loc x)) = 1
    rw [key w hw hp x]
    exact UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw (Ne.symm hap) x
