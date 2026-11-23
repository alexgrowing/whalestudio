import Development.EtaleCohomology.EtaleSheaves.ConeExcision.ExcisionOfConePush

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExcPf

def LeafCokIso : Prop := ∀ (R : Type) [CommRing R] {K' L' K L : Cx R}
  (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L) (w : a ≫ v = u ≫ b),
  (∀ n, IsPushout (a.f n) (u.f n) (v.f n) (b.f n)) → IsIso (cokernel.map a b u v w)

theorem cone_coker (hA1 : A1) (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (a : K ⟶ L)
    (ha : ∀ n, Mono (a.f n)) (n : ℤ) :
    Function.Bijective (HK.pull R (mappingCone.descShortComplex
      (ShortComplex.mk a (cokernel.π a) (cokernel.condition a))) F n) := by
  have : Mono a := HomologicalComplex.mono_of_mono_f a ha
  have hS : (ShortComplex.mk a (cokernel.π a) (cokernel.condition a)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel a) }
  have := mappingCone.quasiIso_descShortComplex hS
  exact hA1 R _ F n

theorem LeafConePush_of (hCok : LeafCokIso) : LeafConePush := by
  intro hA1 R _ F K' L' K L a u v b w ha hb hpo n
  have e1 := Equiv.ofBijective _ (cone_coker hA1 R F a ha n)
  have e2 := Equiv.ofBijective _ (cone_coker hA1 R F b hb n)
  have := hCok R a u v b w hpo
  have e3 := Equiv.ofBijective _ (hA1 R (cokernel.map a b u v w) F n)

  have e : HK R (mappingCone a) F n ≃ HK R (mappingCone b) F n := (e1.symm.trans e3.symm).trans e2
  exact ⟨fun h => e.symm.injective.subsingleton, fun h => e.injective.subsingleton⟩

theorem excision_of_cokernel (hRel : LateralTheory.E.t_E6Cut.LeafRel) (hSq : LeafSq) (hCok : LeafCokIso) :
    LateralTheory.E.t_E6Cut.LeafExc :=
  excision_of_conePush hRel hSq (LeafConePush_of hCok)

end LateralTheory.E.LeafExcPf
