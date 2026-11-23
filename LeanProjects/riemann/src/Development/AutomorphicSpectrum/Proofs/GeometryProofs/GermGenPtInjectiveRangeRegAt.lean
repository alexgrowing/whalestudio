import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegSec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

noncomputable def val (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) {q : X} (hq : genPt ξ ⤳ q) (hqU : q ∈ U)
    (s : Γ(X, U)) :
    genMap ξ ⟨q, hq⟩ ((X.presheaf.germ U q hqU).hom s) = val ξ U h s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold genMap val
  rw [← X.presheaf.germ_stalkSpecializes hqU hq]
  exact (key (X.presheaf.stalkSpecializes hq) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.germ U q hqU) (X.presheaf.stalkSpecializes hq) s).symm).trans
      (key (X.presheaf.germ U q hqU ≫ X.presheaf.stalkSpecializes hq)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_res {V U : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V) (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    val ξ V hV ((X.presheaf.map i.op).hom s) = val ξ U hU s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold val
  rw [← X.presheaf.germ_res i (genPt ξ) hV]
  exact (key (X.presheaf.germ V (genPt ξ) hV) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.map i.op) (X.presheaf.germ V (genPt ξ) hV) s).symm).trans
      (key (X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (val ξ U h) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext X.sheaf U s t (fun q hq => ?_)
  have hq' := hU q hq
  apply hξ.inj ⟨q, hq'⟩
  exact (genMap_germ ξ U h hq' hq s).trans (hst.trans (genMap_germ ξ U h hq' hq t).symm)

theorem mem_range_val_iff (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω) :
    a ∈ (val ξ U h).range ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  constructor
  · intro ha q hqU
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom s, genMap_germ ξ U h q.2 hqU s⟩
  · intro H
    have loc : ∀ q : U, ∃ (W : X.Opens) (t : Γ(X, W)) (_ : (q : X) ∈ W) (hg : genPt ξ ∈ W),
        val ξ W hg t = a := by
      rintro ⟨q, hq⟩
      have hq' : genPt ξ ⤳ q := hU q hq
      obtain ⟨x, hx⟩ := RingHom.mem_range.mp (H ⟨q, hq'⟩ hq)
      obtain ⟨W, hqW, t, ht⟩ := TopCat.Presheaf.germ_exist X.presheaf x
      have hg : genPt ξ ∈ W := hq'.mem_open W.isOpen hqW
      refine ⟨W, t, hqW, hg, ?_⟩
      rw [← genMap_germ ξ W hg hq' hqW t]
      exact (congrArg (genMap ξ ⟨q, hq'⟩) ht).trans hx
    choose W t hqW hg hval using loc
    let V : U → X.Opens := fun q => W q ⊓ U
    have hgV : ∀ q, genPt ξ ∈ V q := fun q => ⟨hg q, h⟩
    let sf : ∀ q : U, Γ(X, V q) := fun q =>
      (X.presheaf.map (homOfLE inf_le_left : V q ⟶ W q).op).hom (t q)
    have hsf : ∀ q, val ξ (V q) (hgV q) (sf q) = a := fun q =>
      (val_res ξ (homOfLE inf_le_left : V q ⟶ W q) (hgV q) (hg q) (t q)).trans (hval q)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
      intro i j
      apply val_injective ξ hξ (V i ⊓ V j) ⟨hgV i, hgV j⟩ (fun q hq => hU q hq.1.2)
      exact ((val_res ξ (TopologicalSpace.Opens.infLELeft (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV i) (sf i)).trans (hsf i)).trans
        ((val_res ξ (TopologicalSpace.Opens.infLERight (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV j) (sf j)).trans (hsf j)).symm
    have hcover : U ≤ iSup V := by
      intro q hq
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hqW ⟨q, hq⟩, hq⟩
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := X.sheaf) (U := V) U
      (fun q => homOfLE inf_le_right) hcover sf hcompat
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    have i0 : U := ⟨genPt ξ, h⟩
    exact (val_res ξ (homOfLE inf_le_right : V i0 ⟶ U) (hgV i0) h s).symm.trans
      ((congrArg (val ξ (V i0) (hgV i0)) (hs i0)).trans (hsf i0))

end GlobalTheory.CompanionTheory.Ar.RegSec

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X),
    IsCptGen ξ → ∀ (U : X.Opens) (h : genPt ξ ∈ U), (∀ q : X, q ∈ U → genPt ξ ⤳ q) →
      Function.Injective (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom ∧
      ∀ a : Ω, a ∈ (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom.range ↔
        ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  intro X Ω _ ξ hξ U h hU
  exact ⟨RegSec.val_injective ξ hξ U h hU, RegSec.mem_range_val_iff ξ hξ U h hU⟩

end GlobalTheory.CompanionTheory.Ar
