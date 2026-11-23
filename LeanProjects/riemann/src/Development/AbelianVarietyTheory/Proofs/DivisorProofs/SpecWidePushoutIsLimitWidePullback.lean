import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem specAdj_symm_comp_specMap (T : Scheme.{0}) {R S : CommRingCat.{0}}
    (f : T ⟶ Spec S) (φ : R ⟶ S) :
    ((ΓSpec.adjunction.homEquiv T (op R)).symm (f ≫ Spec.map φ)).unop =
      φ ≫ ((ΓSpec.adjunction.homEquiv T (op S)).symm f).unop := by
  have h := ΓSpec.adjunction.homEquiv_naturality_right_symm (X := T) (Y := op S) (Y' := op R)
    f φ.op
  exact congrArg Quiver.Hom.unop h

theorem spec_widePushout_isLimit : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  intro n C D A _ _ _ a b l hl H
  classical
  let adj := ΓSpec.adjunction
  let e : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}), (op Γ(T, ⊤) ⟶ op R) ≃ (T ⟶ Spec R) :=
    fun T R => adj.homEquiv T (op R)
  have hcomp : ∀ (T : Scheme.{0}) {R S : CommRingCat.{0}} (f : T ⟶ Spec S) (φ : R ⟶ S),
      ((e T R).symm (f ≫ Spec.map φ)).unop = φ ≫ ((e T S).symm f).unop :=
    fun T R S f φ => specAdj_symm_comp_specMap T f φ
  have hse : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (ψ : R ⟶ Γ(T, ⊤)),
      ((e T R).symm (e T R ψ.op)).unop = ψ := fun T R ψ => by
    rw [Equiv.symm_apply_apply]; rfl
  have hinj : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (f g : T ⟶ Spec R),
      ((e T R).symm f).unop = ((e T R).symm g).unop → f = g :=
    fun T R f g h => (e T R).symm.injective (Quiver.Hom.unop_inj h)

  let gOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      Fin n → (D →+* Γ(t.pt, ⊤)) :=
    fun t i => ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop.hom
  let cOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      C →+* Γ(t.pt, ⊤) :=
    fun t => ((e t.pt (CommRingCat.of C)).symm t.base).unop.hom
  have hgc : ∀ t i, (gOf t i).comp a = cOf t := by
    intro t i
    have h1 := hcomp t.pt (t.π i) (CommRingCat.ofHom a)
    rw [t.condition i] at h1
    have h2 := congrArg CommRingCat.Hom.hom h1
    simpa [gOf, cOf] using h2.symm
  let uOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), A →+* Γ(t.pt, ⊤) := fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose
  have huOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), (uOf t).comp b = cOf t ∧ ∀ i, (uOf t).comp (l i) = gOf t i :=
    fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.1
  have huniq : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))) (u : A →+* Γ(t.pt, ⊤)), u.comp b = cOf t → (∀ i, u.comp (l i) = gOf t i) →
      u = uOf t :=
    fun t u h1 h2 => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.2 u ⟨h1, h2⟩
  refine ⟨WidePullbackCone.IsLimit.mk _
    (fun t => e t.pt (CommRingCat.of A) (CommRingCat.ofHom (uOf t)).op) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).1
  · intro t i
    rw [WidePullbackCone.mk_π]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).2 i
  · intro t m hb hπ
    rw [WidePullbackCone.mk_base] at hb
    simp only [WidePullbackCone.mk_π] at hπ
    have hu : ((e t.pt (CommRingCat.of A)).symm m).unop.hom = uOf t := by
      apply huniq
      · have hb' : m ≫ Spec.map (CommRingCat.ofHom b) = t.base := hb
        have h1 : ((e t.pt (CommRingCat.of C)).symm t.base).unop =
            CommRingCat.ofHom b ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hb']; exact hcomp t.pt m (CommRingCat.ofHom b)
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
      · intro i
        have hπ' : m ≫ Spec.map (CommRingCat.ofHom (l i)) = t.π i := hπ i
        have h1 : ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop =
            CommRingCat.ofHom (l i) ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hπ']; exact hcomp t.pt m (CommRingCat.ofHom (l i))
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
    apply hinj
    rw [hse, ← hu]
    rfl

end GlobalTheory
