import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem ΓSpecIso_inv_comp_specMap_appTop {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

theorem factors_quot_iff (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I),
      w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ P hP
    have h := congrArg (fun k => k.hom P)
      (ΓSpecIso_inv_comp_specMap_appTop w (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change ((w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom P)) = 0
    rw [h, Ideal.Quotient.eq_zero_iff_mem.2 hP, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of (MvPolynomial (Fin n) Rg) ⟶ Γ(T, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv ≫ g.appTop
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom h)), ?_⟩
    rw [Category.assoc, ← Spec.map_comp]
    change T.toSpecΓ ≫ Spec.map φ = g
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv,
      ΓSpecIso_inv_comp_specMap_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.FormsLocus
