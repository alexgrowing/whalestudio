import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.SmoothNearbyCycles

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FormalInv.Fib

variable {O : Type} [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]

abbrev toBase {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ g

theorem toBase_comp {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) :
    Spec.map (CommRingCat.ofHom (u : C →+* B)) ≫ toBase g C = toBase g B := by
  rw [toBase, toBase, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

abbrev fib {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : Scheme.{0} :=
  GlobalTheory.NCyc.gfib Ω (toBase g C)

def fibMap {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) : fib Ω g B ⟶ fib Ω g C :=
  GlobalTheory.NCyc.gfibMap Ω (Spec.map (CommRingCat.ofHom (u : C →+* B))) (toBase_comp g u)

def fibStr {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : fib Ω g C ⟶ GlobalTheory.NCyc.gfib Ω g :=
  GlobalTheory.NCyc.gfibMap Ω (Spec.map (CommRingCat.ofHom (algebraMap A C))) rfl

theorem fibMap_comp {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B D : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] [CommRing D] [Algebra A D] (u : C →ₐ[A] B)
    (v : B →ₐ[A] D) : fibMap Ω g (v.comp u) = fibMap Ω g v ≫ fibMap Ω g u := by
  apply pullback.hom_ext
  · simp only [fibMap, Category.assoc, GlobalTheory.NCyc.gfibMap_fst, GlobalTheory.NCyc.gfibMap_fst_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  · simp only [fibMap, Category.assoc, GlobalTheory.NCyc.gfibMap_snd]

theorem fibMap_str {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) :
    fibMap Ω g u ≫ fibStr Ω g C = fibStr Ω g B := by
  apply pullback.hom_ext
  · simp only [fibMap, fibStr, Category.assoc, GlobalTheory.NCyc.gfibMap_fst, GlobalTheory.NCyc.gfibMap_fst_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  · simp only [fibMap, fibStr, Category.assoc, GlobalTheory.NCyc.gfibMap_snd]

end GlobalTheory.FormalInv.Fib

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FormalInv.Tors

open GlobalTheory.FormalInv.Fib GlobalTheory.NCyc

variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
variable (K : Type) [Field K] [Algebra O K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
variable [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
variable {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {x : SpecialPoint p}

end GlobalTheory.FormalInv.Tors

end
