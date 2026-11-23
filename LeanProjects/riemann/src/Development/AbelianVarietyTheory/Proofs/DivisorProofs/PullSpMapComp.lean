import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  AddMonoidAlgebra.mapRingHom ℤ f

namespace GmPhiNat

theorem laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (laurentMap f).comp (LaurentPolynomial.C : A →+* LaurentPolynomial A) = (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f := by
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a)
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]; rfl

theorem laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n (1 : A)) = AddMonoidAlgebra.single n (1 : B)
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem laurentMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    laurentMap (g.comp f) = (laurentMap g).comp (laurentMap f) :=
  AddMonoidAlgebra.mapRingHom_comp _ _

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem pull_spMap_comp (q : ℕ) {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) (n i : ℤ)
    (x : Ht q (sp A) n i) : pull _ (spMap (g.comp f)) _ n x = pull _ (spMap g) _ n (pull _ (spMap f) _ n x) := by
  rw [spMap_comp, pull_comp]

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f (tw q i) n x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar A) = laurentVar B := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f))
  have h2 := congrArg (fun φ => φ.hom (LaurentPolynomial.T 1)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [laurentVar, laurentVarUnit, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← h2, laurentMap_T]

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
  have h := (hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)).map
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom
  simpa using h

end GmPhiNat

open GmPhiNat in

theorem gmPhi_nat (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hq : IsUnit (q : A))
    (i : ℤ) (a : Ht q (sp A) 0 (i - 1)) :
    pull _ (spMap (laurentMap f)) _ 1 (gmPhi q A i a) = gmPhi q B i (pull _ (spMap f) _ 0 a) := by
  obtain ⟨hcup, -, -, hkum⟩ := h6 q
  simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [pull_cast, hcup, ← pull_spMap_comp, ← pull_spMap_comp, laurentMap_C]
  congr 2
  rw [spMap, hkum _ _ (isUnit_gamma q A hq), laurentVar_map]

end GlobalTheory.EtC

end
