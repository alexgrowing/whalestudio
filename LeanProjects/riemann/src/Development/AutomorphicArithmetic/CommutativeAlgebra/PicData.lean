import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem

open CategoryTheory TensorProduct

noncomputable section

namespace UpperTheory.PicD

section Rings
variable (A C : Type) [CommRing A] [CommRing C] [Algebra A C]

abbrev i1 : C →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.includeLeft

abbrev i2 : C →ₐ[A] C ⊗[A] C := Algebra.TensorProduct.includeRight

abbrev c12 : C ⊗[A] C →ₐ[A] C ⊗[A] (C ⊗[A] C) :=
  Algebra.TensorProduct.map (AlgHom.id A C) (i1 A C)

abbrev c13 : C ⊗[A] C →ₐ[A] C ⊗[A] (C ⊗[A] C) :=
  Algebra.TensorProduct.map (AlgHom.id A C) (i2 A C)

abbrev c23 : C ⊗[A] C →ₐ[A] C ⊗[A] (C ⊗[A] C) := Algebra.TensorProduct.includeRight

variable {A C}

def theta (g : C ⊗[A] C) : C →ₗ[C] C ⊗[A] C := LinearMap.toSpanSingleton C _ g

@[simp] theorem theta_apply (g : C ⊗[A] C) (b : C) : theta g b = b • g := rfl

abbrev Mg (g : C ⊗[A] C) : Submodule A C := GlobalTheory.FlatDescent.invariants (theta g)

end Rings

structure Data where
  S0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}
  S1 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}
  d : S0 ⟶ S1
  ι : ∀ R : CommRingCat.{0}, Additive Rˣ →+ S0.obj R
  ι_nat : ∀ {R R' : CommRingCat.{0}} (f : R ⟶ R') (u : Rˣ),
    (S0.map f).hom (ι R (Additive.ofMul u)) = ι R' (Additive.ofMul (Units.map f.hom.toMonoidHom u))
  ι_inj : ∀ R, Function.Injective (ι R)
  d_eq_zero : ∀ (R : CommRingCat.{0}) (w : S0.obj R), (d.app R).hom w = 0 ↔ ∃ u, ι R u = w
  glue : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C] [Algebra.Etale A C]
    (w : S0.obj (CommRingCat.of C)),
    (S0.map (CommRingCat.ofHom (i1 A C).toRingHom)).hom w = (S0.map (CommRingCat.ofHom (i2 A C).toRingHom)).hom w →
    ∃ y : S0.obj (CommRingCat.of A), (S0.map (CommRingCat.ofHom (algebraMap A C))).hom y = w
  sep : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C] [Algebra.Etale A C],
    Function.Injective (S1.map (CommRingCat.ofHom (algebraMap A C))).hom

namespace Data
variable (P : Data)

def r0 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    P.S0.obj (CommRingCat.of R) →+ P.S0.obj (CommRingCat.of S) := (P.S0.map (CommRingCat.ofHom f)).hom

def r1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    P.S1.obj (CommRingCat.of R) →+ P.S1.obj (CommRingCat.of S) := (P.S1.map (CommRingCat.ofHom f)).hom

def dd (R : Type) [CommRing R] : P.S0.obj (CommRingCat.of R) →+ P.S1.obj (CommRingCat.of R) :=
  (P.d.app (CommRingCat.of R)).hom

def un {R : Type} [CommRing R] (u : Rˣ) : P.S0.obj (CommRingCat.of R) :=
  P.ι (CommRingCat.of R) (Additive.ofMul u)

theorem mapDegZero_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : P.S0.obj (CommRingCat.of R)) : P.r0 g (P.r0 f x) = P.r0 (g.comp f) x := by
  simp [r0, CommRingCat.ofHom_comp]

theorem mapDegOne_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : P.S1.obj (CommRingCat.of R)) : P.r1 g (P.r1 f x) = P.r1 (g.comp f) x := by
  simp [r1, CommRingCat.ofHom_comp]

theorem diff_mapDegZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : P.S0.obj (CommRingCat.of R)) :
    P.dd S (P.r0 f x) = P.r1 f (P.dd R x) := by
  have := congrArg (fun φ => φ.hom x) (P.d.naturality (CommRingCat.ofHom f))
  simpa [dd, r0, r1] using this

theorem mapDegZero_ofUnit {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) :
    P.r0 f (P.un u) = P.un (Units.map f.toMonoidHom u) :=
  P.ι_nat (CommRingCat.ofHom f) u

theorem un_mul {R : Type} [CommRing R] (u v : Rˣ) : P.un (u * v) = P.un u + P.un v :=
  map_add (P.ι (CommRingCat.of R)) (Additive.ofMul u) (Additive.ofMul v)

theorem un_injective {R : Type} [CommRing R] : Function.Injective (P.un (R := R)) :=
  fun _ _ h => Additive.ofMul.injective (P.ι_inj _ h)

theorem un_one {R : Type} [CommRing R] : P.un (1 : Rˣ) = 0 := map_zero (P.ι (CommRingCat.of R))

theorem dd_eq_zero {R : Type} [CommRing R] (w : P.S0.obj (CommRingCat.of R)) :
    P.dd R w = 0 ↔ ∃ u : Rˣ, P.un u = w := by
  rw [dd, P.d_eq_zero]
  exact ⟨fun ⟨u, h⟩ => ⟨u.toMul, h⟩, fun ⟨u, h⟩ => ⟨Additive.ofMul u, h⟩⟩

structure Triv {A : Type} [CommRing A] (z : P.S1.obj (CommRingCat.of A)) (M : Type) [AddCommGroup M] [Module A M]
    (C : Type) [CommRing C] [Algebra A C] (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C) :
    Prop where
  dw : P.dd C w = P.r1 (algebraMap A C) z
  hg : P.un g = P.r0 (i2 A C).toRingHom w - P.r0 (i1 A C).toRingHom w
  ht : ∀ m, t m • (g : C ⊗[A] C) = (1 : C) ⊗ₜ[A] t m
  bij : Function.Bijective (LinearMap.liftBaseChange C t)

def Rel {A : Type} [CommRing A] (z : P.S1.obj (CommRingCat.of A)) (M : Type) [AddCommGroup M] [Module A M] : Prop :=
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
    ∃ (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C), P.Triv z M C w g t

def LocEx {A : Type} [CommRing A] (z : P.S1.obj (CommRingCat.of A)) : Prop :=
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
    ∃ w : P.S0.obj (CommRingCat.of C), P.dd C w = P.r1 (algebraMap A C) z

end Data
end UpperTheory.PicD
