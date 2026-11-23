import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTateA

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem locfin_of (hF : SgcField) : Formalism.GaloisCohomology.LocalFinitenessK := by
  intro l _ K hK r M _ _ _ _ _ rho hr hc
  obtain ⟨hsep, v, t, hloc, -⟩ := hF l K hK
  let : ValuativeRel ↥K := v
  let : TopologicalSpace ↥K := t
  have : IsNonarchimedeanLocalField ↥K := hloc
  have : IsSepClosure ↥K (PadicAlgCl l) := hsep
  obtain ⟨A, hA, e, he⟩ := gcRep (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho hc
  have : IsDiscreteRep A := hA
  have : Finite A := Finite.of_equiv M e.toEquiv
  have hcard : Nat.card A = Nat.card M := (Nat.card_congr e.toEquiv).symm
  have hM : (Nat.card A : ↥K) ≠ 0 := by
    rw [hcard]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨e0, -⟩ := gc0 (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he
  obtain ⟨e1, -⟩ := gc1 (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he
  obtain ⟨e2, -⟩ := gc2 (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he
  refine ⟨?_, ?_, ?_, fun n hn => ?_⟩
  · have := finite_cohomology_localField A hM 0
    exact Finite.of_equiv _ e0.symm.toEquiv
  · have := finite_cohomology_localField A hM 1
    exact Finite.of_equiv _ e1.symm.toEquiv
  · have := finite_cohomology_localField A hM 2
    exact Finite.of_equiv _ e2.symm.toEquiv
  · obtain ⟨en⟩ := gcn (Formalism.GaloisCohomology.GK l K) (ZMod (l ^ r)) M rho A e he n
    have := subsingleton_cohomology_localField A hM n hn
    exact en.toEquiv.subsingleton

end CompanionTheory.LocalTateOrthogonality.Gcoh
