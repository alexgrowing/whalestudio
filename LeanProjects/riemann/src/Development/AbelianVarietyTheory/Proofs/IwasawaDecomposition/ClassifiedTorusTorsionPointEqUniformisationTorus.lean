import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.TorusTorsionPoint

theorem eq_torus_of_classify : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), FormalEq P.U.toUnifPre x₀ g₀ → ∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) (τ : Multiplicative P.D.toPre.X →* A'ˣ) (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → ∀ (g : GtPt P.D.toPre (Over.mk (spMap (f.comp a)))), (∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) → ∀ (h : Over.mk (spMap (f.comp a)) ⟶ N), GtPt.IsPull h.left g₀ g → h.left ≫ x₀.left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ := by
  intro E _ _ _ H R _ _ _ t P N g₀ x₀ hform A A' _ _ a ha f t₀ m₀ τ z hz g hg h hpull
  have ha' : ∀ x ∈ maximalIdeal R, (f.comp a) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, ha x hx, map_zero]
  have hρ := GlobalTheory.TorusPart.map_pow_one_eq_zero ha
  have hρ' := GlobalTheory.TorusPart.map_pow_one_eq_zero ha'
  have eR : (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ =
      (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X ≫ (P.U.gt 0).i.left) ≫
        pullback.fst t.G.hom (thick R (maximalIdeal R) 0) := by
    rw [Over.comp_left, Category.assoc]
    have k := GlobalTheory.TorusPart.gtTorus_left (P.U.gt 0) hρ m₀.cart
    exact (congrArg (z.left ≫ ·) k).trans (by simp only [Category.assoc])
  have hN : (h.left ≫ x₀.left) ≫ t.G.hom = GlobalTheory.TorusPart.thickPt 0 hρ' ≫ thick R (maximalIdeal R) 0 := by
    rw [GlobalTheory.TorusPart.thickPt_thick, Category.assoc, Over.w x₀, Over.w h]; rfl
  let y₁ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 t.G).left :=
    pullback.lift (h.left ≫ x₀.left) (GlobalTheory.TorusPart.thickPt 0 hρ') hN
  let y₂ : Sp A' ⟶ (thickObj R (maximalIdeal R) 0 t.G).left :=
    z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X ≫ (P.U.gt 0).i.left
  have e₁ : h.left ≫ x₀.left = y₁ ≫ pullback.fst t.G.hom (thick R (maximalIdeal R) 0) :=
    (pullback.lift_fst _ _ _).symm
  have hP := (GlobalTheory.TorsionFormCompare.formalEq_iff P.U.toUnifPre x₀ g₀).1 hform
  have hc := hP 0 (Sp A') h.left y₁ e₁.symm
  obtain ⟨hb, hv⟩ := (GlobalTheory.FormalPoint.hasCoords_iff _ 0 g₀ h.left y₁).1 hc
  suffices hy : y₁ = y₂ by rw [eR, e₁, hy]
  refine GlobalTheory.TorusCoord.ext_of_val (P.U.gt 0) y₁ y₂ ?_ ?_
  · rw [hb, ← hpull.1, (hg 0).1, GlobalTheory.TorusCoord.pG_left]
    have hk : (P.U.gt 0).i.left ≫ (P.U.gt 0).q.left =
        (splitTorus _ P.D.toPre.X).hom ≫ eSec (thickObj R (maximalIdeal R) 0 P.D.toPre.P.A) := by
      have := congrArg Over.Hom.left (P.U.gt 0).isKernel.w
      rw [Over.comp_left, Over.comp_left] at this
      exact this
    have hE : eSec (thickObj R (maximalIdeal R) 0 P.D.toPre.P.A) ≫
        pullback.fst P.D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
        thick R (maximalIdeal R) 0 ≫ eSec P.D.toPre.P.A :=
      GlobalTheory.UnitValue.eSec_pullback_fst _ _
    have hz' : z.left ≫ (splitTorus (Sp A) P.D.toPre.X).hom = spMap f := Over.w z
    have hfa : spMap f ≫ spMap a = spMap (f.comp a) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    simp only [y₂, Category.assoc]
    rw [reassoc_of% hk, hE, ← Category.assoc (GlobalTheory.SplitTorus.bcMap _ _), GlobalTheory.SplitTorus.bcMap_hom,
      Category.assoc, reassoc_of% (GlobalTheory.TorusPart.thickPt_thick hρ), reassoc_of% hz', reassoc_of% hfa]
    rfl
  · intro χ w J hJ
    rw [hv χ w J hJ]
    have l₁ : val (g₀.s χ) h.left w J = gm (𝟙 _) w ⊤ (unitOn (τ (Multiplicative.ofAdd χ))) := by
      have c₁ := val_corr hJ (hpull.2 χ) (𝟙 _)
      rw [val_pull hJ, Category.id_comp] at c₁
      exact c₁.symm.trans (GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) (𝟙 _) hJ)
    rw [l₁]
    let Z₀ : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :=
      Over.mk ((z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X) ≫
        (splitTorus _ P.D.toPre.X).hom)
    let τ' : Z₀ ⟶ splitTorus _ P.D.toPre.X :=
      Over.homMk (z.left ≫ GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hρ) P.D.toPre.X) rfl
    have k := GlobalTheory.TorusCoord.val_t_act (P.U.gt 0) τ' 1 χ (𝟙 Z₀.left) w J hJ
    have k₁ : 𝟙 Z₀.left ≫ (τ' ≫ (P.U.gt 0).i * 1).left = y₂ := by
      rw [_root_.mul_one, Category.id_comp, Over.comp_left]
      simp only [τ', y₂, Over.homMk_left, Category.assoc]
    have k₂ : val ((P.U.gt 0).t χ) (𝟙 Z₀.left ≫ (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 t.G).left) w J = 1 := by
      have e : (1 : Z₀ ⟶ thickObj R (maximalIdeal R) 0 t.G).left = Z₀.hom ≫ eSec (thickObj R (maximalIdeal R) 0 t.G) := by
        rw [Hom.one_def, Over.comp_left]; rfl
      rw [e, Category.id_comp, ← val_pull hJ, val_corr hJ ((P.U.gt 0).t_unit χ), val_one]
    have k₃ : GlobalTheory.splitTorusPointsEquiv _ P.D.toPre.X Z₀ τ' (Multiplicative.ofAdd χ) =
        unitOn (τ (Multiplicative.ofAdd χ)) := by
      refine Units.ext ?_
      rw [← hz χ, GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val]
      simp only [τ', Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        GlobalTheory.SplitTorus.bcMap_appTop_chi]
    rw [k₁, k₂, k₃, _root_.mul_one] at k
    exact k.symm

end GlobalTheory.TorusTorsionPoint
