import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem stalkId_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) (y : Y) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.ofIdealTop K) y = K.map (Y.presheaf.germ ⊤ y trivial).hom := by
  rw [ds_stalkId_eq_map _ ⟨⊤, isAffineOpen_top Y⟩ y trivial, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_map, ← CommRingCat.hom_comp]
  congr 2
  exact Y.presheaf.germ_res (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) y (by trivial)

theorem ideal_top_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top Y⟩ = K := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have : Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [← Y.presheaf.map_id]; rfl
  rw [this]
  simp

theorem comap_eq_ofIdealTop (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    J.comap χ = Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom) := by
  refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
  have hz : χ z ∈ U.1 := hle trivial
  rw [stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
  congr 3
  exact (Sp R).presheaf.germ_res (homOfLE hle) z (by trivial)

theorem idlAlong_eq_idealAlong (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) : idlAlong J χ = idealAlong J χ := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  unfold idlAlong idealAlong
  rw [comap_eq_ofIdealTop X J R χ ⟨U, hU⟩ hle, ideal_top_ofIdealTop, ds_stalkId_eq_map J ⟨U, hU⟩ _ hx,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

end GlobalTheory.LocM
