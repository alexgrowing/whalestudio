import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def secAlg {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) : A →+* Γ(T, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h
  rfl

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.kappa_comm {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.Opens) (a : A) :
    ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
      (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((I.subschemeι ≫ pullback.snd _ g).app U).hom (_root_.GlobalTheory.HilbAff.secAlg A g U a) := by
  have key : (I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B =
      (I.subschemeι ≫ pullback.snd _ g) ≫ g := by
    simp [pullback.condition]
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (_root_.GlobalTheory.HilbAff.str A B).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    have := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hm : (_root_.GlobalTheory.HilbAff.str A B).appTop ≫
      (I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp) = g.appLE ⊤ U (by simp) ≫ (I.subschemeι ≫ pullback.snd _ g).app U := by
    calc _ = ((I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = ((I.subschemeι ≫ pullback.snd _ g) ≫ g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          _root_.GlobalTheory.HilbAff.appLE_eq_of_eq key _ _ _ _
      _ = _ := by
        rw [Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) hm

def kappa {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((I.subschemeι ≫ pullback.snd _ g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => kappa_comm A B g I U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem kappa_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    kappa A B g I U (c ⊗ₜ[A] b) = ((I.subschemeι ≫ pullback.snd _ g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

def xI (C : Type) [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) :
    (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv).ker

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.basic_iff_kappa {r N : ℕ} (e : Module.Basis (Fin N) A B)
    (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (hI : _root_.GlobalTheory.HilbAff.Good A B r g I) :
    _root_.GlobalTheory.HilbAff.Basic A B e σ (T := T) ⟨g, ⟨I, hI⟩⟩ ↔ ∀ U : T.affineOpens,
      letI := (_root_.GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      Function.Bijective fun c : Fin r → Γ(T, U) =>
        _root_.GlobalTheory.HilbAff.kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k)) := by
  unfold _root_.GlobalTheory.HilbAff.Basic
  refine forall_congr' fun U => ?_
  simp only [map_sum, _root_.GlobalTheory.HilbAff.kappa_tmul]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_res {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) {U V : T.Opens}
    (h : U ≤ V) : (T.presheaf.map (homOfLE h).op).hom.comp (_root_.GlobalTheory.HilbAff.secAlg A g V) =
      _root_.GlobalTheory.HilbAff.secAlg A g U := by
  ext a
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_comp {C : Type} [CommRing C] {T : Scheme.{0}}
    (h : T ⟶ Spec (CommRingCat.of C)) (f : A →+* C) (U : T.Opens) :
    _root_.GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom f)) U =
      (_root_.GlobalTheory.HilbAff.secAlg C h U).comp f := by
  have hm : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (h ≫ Spec.map (CommRingCat.ofHom f)).appLE ⊤ U (by simp) =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) :=
    calc _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop ≫ h.appLE ⊤ U (by simp) :=
          congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h _ ⊤ U _)
      _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop) ≫ h.appLE ⊤ U (by simp) :=
          (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv) ≫
          h.appLE ⊤ U (by simp) := by rw [← Scheme.ΓSpecIso_inv_naturality]
      _ = _ := Category.assoc _ _ _
  ext a
  exact congrArg (fun φ => φ.hom a) hm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.eq_of_secAlg_top {T : Scheme.{0}}
    {g₁ g₂ : T ⟶ Spec (CommRingCat.of A)}
    (h : _root_.GlobalTheory.HilbAff.secAlg A g₁ ⊤ = _root_.GlobalTheory.HilbAff.secAlg A g₂ ⊤) :
    g₁ = g₂ := by
  apply ext_of_isAffine
  have e₁ : g₁.appLE ⊤ ⊤ le_top = g₁.appTop := g₁.appLE_eq_app
  have e₂ : g₂.appLE ⊤ ⊤ le_top = g₂.appTop := g₂.appLE_eq_app
  have h' : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₁.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₂.appLE ⊤ ⊤ le_top := CommRingCat.hom_ext h
  rw [e₁, e₂] at h'
  exact (cancel_epi _).1 h'

end GlobalTheory.HilbAff
