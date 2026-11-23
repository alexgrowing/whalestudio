import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem flagPt_germ_cellGL_eq_fromSpecStalk (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (y : Fl ι N)
    (hy : y ∈ cellOpen ι N w) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map
      (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)) =
      (Fl ι N).fromSpecStalk y := by
  have hU : IsAffineOpen (cellOpen ι N w) :=
    (isAffineOpen_top (Sp (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).image_of_isOpenImmersion _
  have key : spMap (cellRing ι N w) ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = hU.fromSpec := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) hU
      (isAffineOpen_top _) (Scheme.Hom.preimage_image_eq _ ⊤).ge
    have e₀ : ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).hom =
        (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appLE (cellOpen ι N w) ⊤
          (Scheme.Hom.preimage_image_eq _ ⊤).ge :=
      Scheme.Hom.appIso_hom' _ _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← e₀] at h
    have e : spMap (cellRing ι N w) = Spec.map ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).inv := by
      exact Spec.map_comp _ _
    rw [e]
    erw [Category.assoc, ← h]
    erw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  rw [← spMap_flagPt, ← cell, ← hU.fromSpecStalk_eq_fromSpecStalk hy, IsAffineOpen.fromSpecStalk, ← key]
  rw [spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

end GlobalTheory.FlagZ.Univ
