import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open LateralTheory.E.E4 LateralTheory.E.StrictHenselianNeighbourhood

namespace UpperTheory.Cb

private theorem factor_later {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (E : Type) [CommRing E] [Algebra (D.obj j) E] [Algebra.Etale (D.obj j) E]
    (ψ : E →+* Ω)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E)) = l j) :
    ∃ (k : J) (g : j ⟶ k) (φ : E →+* D.obj k), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
      l k ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  let π : Sp E ⟶ Sp (D.obj j) := Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E))
  haveI hπ : Etale π := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  haveI : IsIso (e j) := he j
  let q : Sp E ⟶ (V j).left := π ≫ e j
  let W : B.Etale := Scheme.Etale.mk (q ≫ (V j).hom)
  let bj : W ⟶ V j := MorphismProperty.Over.homMk q rfl
  have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ q = l j ≫ e j := by
    rw [← hψ]; simp [q, π]
  have hs : Spec.map (CommRingCat.ofHom ψ) ≫ q ≫ (a j).left = s := by
    rw [reassoc_of% hpt, hl]
  obtain ⟨k, g, hg, hgl⟩ := hcof W (bj ≫ a j) (Spec.map (CommRingCat.ofHom ψ)) hs
  obtain ⟨g', hg', hgl'⟩ : ∃ g' : (V k).left ⟶ Sp E, g' ≫ q ≫ (a j).left = (a k).left ∧
      l k ≫ e k ≫ g' = Spec.map (CommRingCat.ofHom ψ) := ⟨g, hg, hgl⟩
  clear hg hgl g hs
  let m := IsFiltered.max j k
  let u : j ⟶ m := IsFiltered.leftToMax j k
  let v : k ⟶ m := IsFiltered.rightToMax j k
  haveI : IsIso (e m) := he m
  let g1 : (V m).left ⟶ (V j).left :=
    inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map u).hom) ≫ e j
  let g2 : (V m).left ⟶ (V j).left :=
    inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map v).hom) ≫ e k ≫ g' ≫ q
  have h1 : g1 ≫ (a j).left = (a m).left := by
    simp only [g1, Category.assoc]; rw [hcomp j m u]; simp
  have h2 : g2 ≫ (a j).left = (a m).left := by
    simp only [g2, Category.assoc]; rw [hg', hcomp k m v]; simp
  have h3 : l m ≫ e m ≫ g1 = l m ≫ e m ≫ g2 := by
    simp only [g1, g2, IsIso.hom_inv_id_assoc]
    rw [reassoc_of% (hlc j m u), reassoc_of% (hlc k m v), reassoc_of% hgl', hpt]
  obtain ⟨n, w, hw⟩ := heq (V j) (a j) m g1 g2 h1 h2 h3
  simp only [g1, g2, IsIso.hom_inv_id_assoc] at hw
  let h : Sp (D.obj n) ⟶ Sp E :=
    Spec.map (CommRingCat.ofHom (D.map w).hom) ≫ Spec.map (CommRingCat.ofHom (D.map v).hom) ≫
      e k ≫ g'
  have hh : h ≫ π = Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) := by
    rw [← cancel_mono (e j)]
    have : Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) =
        Spec.map (CommRingCat.ofHom (D.map w).hom) ≫ Spec.map (CommRingCat.ofHom (D.map u).hom) := by
      rw [← Spec.map_comp]; simp
    rw [this]
    simp only [Category.assoc]
    rw [hw]
    simp [h, q]
  refine ⟨n, u ≫ w, (Spec.preimage h).hom, ?_, ?_⟩
  · have h4 : Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E) ≫ Spec.preimage h) =
        Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) := by
      rw [Spec.map_comp, Spec.map_preimage]; exact hh
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h4)
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    simp only [h]
    rw [reassoc_of% (hlc m n w), reassoc_of% (hlc k m v), hgl']

end UpperTheory.Cb

theorem UpperTheory.Cb.strictlyHenselianLocal_of_negligibleDegree :
    LateralTheory.E.LeafDegCut.LeafNeg → LateralTheory.E.StrictHenselianNeighbourhood.LeafSHHens := by
  intro _ B U x Ω _ _ s J _ _ D c hc V a l e t hP _
  let ρ : ∀ j, D.obj j ⟶ CommRingCat.of Ω := fun j => Spec.preimage (l j)
  have hρ : ∀ j, Spec.map (ρ j) = l j := fun j => Spec.map_preimage _
  have hlc := hP.2.2.2.2.2.1
  have hw : ∀ (j k : J) (f : j ⟶ k), D.map f ≫ ρ k = ρ j := by
    intro j k f
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, hρ, ← hlc j k f]
    rfl
  let cc : Cocone D :=
    { pt := CommRingCat.of Ω
      ι := { app := ρ, naturality := fun j k f => by simpa using hw j k f } }
  let ω : c.pt →+* Ω := (hc.desc cc).hom
  have hω : ∀ j, ω.comp (c.ι.app j).hom = (ρ j).hom := fun j =>
    congrArg CommRingCat.Hom.hom (hc.fac cc j)
  refine LateralTheory.E.LeafSHSysPf.SHofCof D c hc ⟨Ω, inferInstance, inferInstance, ω, ?_⟩
  intro j E _ _ _ ψ hψ
  obtain ⟨k, g, φ, h1, h2⟩ := factor_later U x Ω s D c V a l e t hP j E ψ (by
    rw [← Spec.map_comp, ← hρ j]
    congr 1
    apply CommRingCat.hom_ext
    rw [hω j] at hψ
    exact hψ)
  refine ⟨k, g, φ, h1, ?_⟩
  rw [← RingHom.comp_assoc, hω k]
  have h3 : CommRingCat.ofHom φ ≫ ρ k = CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ]
    exact h2
  exact congrArg CommRingCat.Hom.hom h3
