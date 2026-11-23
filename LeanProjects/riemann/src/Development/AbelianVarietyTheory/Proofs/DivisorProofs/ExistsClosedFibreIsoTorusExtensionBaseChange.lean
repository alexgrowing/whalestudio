import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackThickeningOfCarriesTorusCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closedFibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∃ (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' ∧ GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' ∧ IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' := by
  intro R _ _ _ hR D C Y W _ _ _ T
  haveI := T.loc
  let κ : ResidueField R →+* ResidueField W := ResidueField.map T.φ
  have hκ : κ.comp (residue R) = (residue W).comp T.φ := RingHom.ext fun r => ResidueField.map_residue T.φ r
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.FormalModel.exists_carries T.hD Y.rep (T.U.gt 0)
  have gA := GlobalTheory.T.isGrpPullback_thickening_of_carries_torusCoordinates T.hD T.U.toUnifPre Y hφ₀
  have hle : maximalIdeal W ^ (0 + 1) ≤ RingHom.ker (residue W) := by
    rw [zero_add, pow_one, ker_residue]
  let c : W ⧸ maximalIdeal W ^ (0 + 1) →+* ResidueField W :=
    Ideal.Quotient.lift _ (residue W) fun a ha => (RingHom.mem_ker).1 (hle ha)
  have hc : spMap c ≫ thick W (maximalIdeal W) 0 = spMap (residue W) := by
    rw [show thick W (maximalIdeal W) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have hc' : spMap c ≫ thick W (maximalIdeal W) 0 ≫ spMap T.φ = spMap κ ≫ spMap (residue R) := by
    rw [← Category.assoc, hc, ← spMap_comp, ← spMap_comp, hκ]
  let P := (Over.pullback (spMap c)).obj (thickObj W (maximalIdeal W) 0 T.G)
  have g1 : IsGrpPullback P T.G (spMap (residue W))
      (pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0)) :=
    ((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback T.G (thick W (maximalIdeal W) 0))).congr hc rfl
  obtain ⟨e1, he1, he1'⟩ := grpPullback_iso g1 (isGrpPullback_pullback T.G (spMap (residue W)))
  have g2 : IsGrpPullback P Y.H (spMap κ ≫ spMap (residue R)) (pullback.fst _ _ ≫ φ₀) :=
    ((isGrpPullback_pullback _ (spMap c)).comp gA).congr hc' rfl
  have g3 := (isGrpPullback_pullback ((Over.pullback (spMap (residue R))).obj Y.H) (spMap κ)).comp
    (isGrpPullback_pullback Y.H (spMap (residue R)))
  obtain ⟨e2, he2, he2'⟩ := grpPullback_iso g2 g3
  refine ⟨κ, e1.symm ≪≫ e2, hκ, ?_, ?_⟩
  · haveI := he1; haveI := he2
    show IsMonHom (e1.inv ≫ e2.hom)
    infer_instance
  · intro Z p p' y hp hy
    have i1 : e1.inv.left ≫ pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) =
        pullback.fst T.G.hom (spMap (residue W)) := by
      rw [← he1', ← Category.assoc, ← Over.comp_left, e1.inv_hom_id, Over.id_left, Category.id_comp]
    let g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left := p ≫ e1.inv.left ≫ pullback.fst _ _
    have hy' : y = g ≫ φ₀ := by
      rw [hy]
      have := he2'
      simp only [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc, g]
      rw [this]
    subst hy'
    obtain ⟨ξ', h1, h2⟩ := GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport T.hD T.U.toUnifPre Y hφ₀ Z g
    refine ⟨g, ξ', ?_, h1, h2⟩
    rw [hp]
    show (p ≫ e1.inv.left ≫ pullback.fst _ _) ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) = _
    rw [Category.assoc, Category.assoc, i1]

end GlobalTheory.Mum
