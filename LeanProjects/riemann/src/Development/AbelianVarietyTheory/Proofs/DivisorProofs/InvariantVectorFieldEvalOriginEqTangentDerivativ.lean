import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin

variable {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}

theorem valR_eq_germ (x : Sp A ⟶ X) (U : X.Opens) (hx : x (IsLocalRing.closedPoint A) ∈ U) (f : Γ(X, U)) :
    valR x U f = (X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom f := by
  have e : X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of A) x =
      x.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [e, valR, dif_pos (Scheme.preimage_eq_top_of_closedPoint_mem x hx).ge]
  rfl

end GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem eta_hom : (η[G]).left ≫ G.hom = 𝟙 (Sp R) := Over.w (η[G])

theorem isTr_eta_tv (v : TanM (𝟙 (Sp R)) G) :
    IsTr G (RingHom.id R) (η[G]).left v (tv v).left := by
  have hη := eta_hom G
  refine ⟨1, Over.homMk (tv v).left ?_, ?_, ?_, ?_⟩
  · have := Over.w (tv v)
    simp only [Over.mk_hom, Category.comp_id] at this ⊢
    rw [this, hη, Category.comp_id]
  · rw [one_left]
    simp [hη]
  · have hd : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
      ext x <;> simp [dualMap]
    simp [hd, spMap]
  · rw [_root_.one_mul]
    rfl

theorem evO_germ_of_isInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens)
    (hO : origin G ∈ O) (f : Γ(G.left, O)) :
    evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) =
      tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  have hη := eta_hom G
  have hg : (η[G]).left ≫ G.hom = spMap (RingHom.id R) := by
    rw [hη]; simp [spMap]
  have hO' : (tv v).left (IsLocalRing.closedPoint (DualNumber R)) ∈ O := by
    rw [tv_closedPoint]; exact hO
  have htop : ⊤ ≤ (η[G]).left ⁻¹ᵁ O := (Scheme.preimage_eq_top_of_closedPoint_mem _ hO).ge
  have key := hinv.2 R (RingHom.id R) (η[G]).left (tv v).left O f hg htop (isTr_eta_tv G v)
  rw [valR_eq_germ _ O hO', valR_eq_germ (η[G]).left O hO] at key
  rw [tanDer_eq, evO]
  have e2 : G.left.presheaf.germ O (origin G) hO ≫
      (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G v).symm)).hom =
        G.left.presheaf.germ O _ hO' := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  rw [← CommRingCat.comp_apply, ← Category.assoc, e2]
  exact key.symm
end GlobalTheory.CoordsOrigin
