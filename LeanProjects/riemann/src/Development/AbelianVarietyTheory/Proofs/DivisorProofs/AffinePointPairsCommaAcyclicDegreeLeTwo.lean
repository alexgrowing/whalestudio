import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CatCoh.Desc

universe v u

section Retract

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
  {T : C} (P : ∀ S, (T ⟶ S) → Prop) (Q : C → Prop) (hQ : ∀ S, (T ⟶ S) → Q S)
  (G : ∀ S, Q S → C) (θ : ∀ S h, S ⟶ G S h)
  (p : ∀ S (u : T ⟶ S), G T (hQ T (𝟙 T)) ⟶ G S (hQ S u))
  (m : ∀ S S' (h : Q S) (h' : Q S'), (S ⟶ S') → (G S h ⟶ G S' h'))
  (hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u))
  (hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h')
  (hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ))
  (hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
    m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ))
  (bij : ∀ S h, Function.Bijective (mp F (θ S h)))
  (h0 : P _ (θ T (hQ T (𝟙 T))))

include hQ bij h0 in

theorem sep_of_retract : Sep F P := by
  intro x hx
  refine (bij T (hQ T (𝟙 T))).1 ?_
  rw [hx _ _ h0, map_zero]

include hp bij h0 in

theorem glue_of_retract : Glue F P := by
  intro s hs
  obtain ⟨x, hx⟩ := (bij T (hQ T (𝟙 T))).2 (s _ (θ T (hQ T (𝟙 T))))
  refine ⟨x, fun S u hu ↦ (bij S (hQ S u)).1 ?_⟩
  rw [← mp_comp, ← hp, mp_comp, hx, ← hs _ _ _ _ h0, hp, hs _ _ _ _ hu]

include hp hθ hpm bij h0 in

theorem cocycleOne_vanishing_of_natural_additive_retract : Van1 F P := by
  intro a ha
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S u ↦ Function.surjInv (bij S (hQ S u)).2
    (a _ _ (θ T (hQ T (𝟙 T))) (p S u) - a _ _ u (θ S (hQ S u))), fun S S' u ψ hu ↦ ?_⟩
  refine (bij S' (hQ S' (u ≫ ψ))).1 ?_
  rw [map_sub, e, ← mp_comp, ← hθ S S' (hQ S u) (hQ S' (u ≫ ψ)) ψ, mp_comp, e]
  have k1 := ha _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ) h0
  have k2 := ha _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) hu
  have k3 := ha _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) hu
  rw [hpm, hp] at k1
  rw [hθ] at k3
  simp only [map_sub]
  linear_combination k1 - k3 + k2

include hp hθ hpm hmm bij h0 in

theorem cocycleTwo_vanishing_of_natural_additive_retract : Van2 F P := by
  intro z hz
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S S' u ψ ↦ Function.surjInv (bij S' (hQ S' (u ≫ ψ))).2
    (z _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) - z _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) +
      z _ _ _ (θ T (hQ T (𝟙 T))) (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)),
    fun S S' S'' u ψ χ hu ↦ ?_⟩
  refine (bij S'' (hQ S'' (u ≫ ψ ≫ χ))).1 ?_
  rw [map_add, map_sub, e, e, ← mp_comp,
    ← hθ S' S'' (hQ S' (u ≫ ψ)) (hQ S'' (u ≫ ψ ≫ χ)) χ, mp_comp, e]
  have c1 := hz _ _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) h0
  have c2 := hz _ _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c3 := hz _ _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c4 := hz _ _ _ _ u ψ χ (θ S'' (hQ S'' (u ≫ ψ ≫ χ))) hu
  rw [hpm, hmm, hp] at c1
  rw [hθ, hmm] at c2
  rw [hθ] at c3
  simp only [map_add, map_sub]
  linear_combination c3 - c4 - c2 + c1

end Retract

end GlobalTheory.CatCoh.Desc

namespace GlobalTheory.PDForm

open KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
  GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift GlobalTheory.CatCoh.Desc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem le_preimage_of_hom {T S : (IsSm κ t i).FullSubcategory} (u : T ⟶ S) {V : Y.Opens}
    (hV : ⊤ ≤ (T.obj.T.x ≫ i) ⁻¹ᵁ V) : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V := by
  intro z _
  rw [← u.hom.1.pt, Category.assoc, Scheme.Hom.comp_preimage]
  exact hV trivial

def cutPr (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    (IsSm κ t i).FullSubcategory :=
  ⟨⟨S.obj.T, S.obj.U ⊓ V.1, Or.inl (by
    rcases S.obj.hU with hU | hU
    · exact hY _ _ hU V.2
    · rw [hU, top_inf_eq]; exact V.2), fun z _ ↦ ⟨S.obj.mem trivial, h trivial⟩⟩, ⟨V, h⟩⟩

theorem cutPr_aff (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    IsAffineOpen (cutPr hY V S h).obj.U := by
  rcases S.obj.hU with hU | hU
  · exact hY _ _ hU V.2
  · change IsAffineOpen (S.obj.U ⊓ V.1)
    rw [hU, top_inf_eq]; exact V.2

def prHom {S S' : (IsSm κ t i).FullSubcategory} (φ : S.obj.T ⟶ S'.obj.T) (h : S'.obj.U ≤ S.obj.U) :
    S ⟶ S' :=
  ObjectProperty.homMk ⟨φ, h⟩

theorem prHom_ext {S S' : (IsSm κ t i).FullSubcategory} {f g : S ⟶ S'} (h : f.hom.1 = g.hom.1) :
    f = g :=
  ObjectProperty.hom_ext _ (Subtype.ext h)

theorem isSm_acyclic (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (T : (IsSm κ t i).FullSubcategory) :
    Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  obtain ⟨V, hV⟩ := T.property
  have hQ : ∀ S (u : T ⟶ S), ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1 := fun S u ↦ le_preimage_of_hom u hV
  let θ : ∀ (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1), S ⟶ cutPr hY V S h := fun S h ↦ prHom (𝟙 S.obj.T) inf_le_left
  let p : ∀ S (u : T ⟶ S), cutPr hY V T (hQ T (𝟙 T)) ⟶ cutPr hY V S (hQ S u) :=
    fun S u ↦ prHom u.hom.1 (inf_le_inf_right _ u.hom.2)
  let m : ∀ (S S' : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1)
      (h' : ⊤ ≤ (S'.obj.T.x ≫ i) ⁻¹ᵁ V.1), (S ⟶ S') → (cutPr hY V S h ⟶ cutPr hY V S' h') :=
    fun S S' h h' ψ ↦ prHom ψ.hom.1 (inf_le_inf_right _ ψ.hom.2)
  have hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u) :=
    fun S u ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h' :=
    fun S S' h h' ψ ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ) :=
    fun S S' u ψ ↦ prHom_ext rfl
  have hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
      m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ) :=
    fun S S' S'' h h' h'' ψ χ ↦ prHom_ext rfl
  have bij : ∀ S h, Function.Bijective (mp ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (θ S h)) :=
    fun S h ↦ ⟨fun a b hab ↦ hab, fun y ↦ ⟨y, rfl⟩⟩
  have h0 := cutPr_aff hY V T (hQ T (𝟙 T))
  exact ⟨sep_of_retract _ _ _ hQ _ θ bij h0, glue_of_retract _ _ _ hQ _ θ p hp bij h0,
    cocycleOne_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm bij h0,
    cocycleTwo_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm hmm bij h0⟩

theorem isSm_acyclic_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧
    ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R)
      (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) :=
  ⟨fun _ _ _ _ _ _ _ _ hY T ↦ ⟨(isSm_acyclic hY T).1, (isSm_acyclic hY T).2.1, (isSm_acyclic hY T).2.2.1⟩,
    fun _ _ _ _ _ _ _ _ hY T ↦ (isSm_acyclic hY T).2.2.2⟩

end GlobalTheory.PDForm
