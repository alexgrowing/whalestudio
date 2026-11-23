import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem pullback_map_eq_of_pullTorus_eq {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {p : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G p φ) {X : Type} [AddCommGroup X]
    (f g : splitTorus S X ⟶ G) (e : GlobalTheory.TorusPart.pullTorus h f = GlobalTheory.TorusPart.pullTorus h g) :
    (Over.pullback p).map f = (Over.pullback p).map g := by
  have k : GlobalTheory.SplitTorus.bcMap p X ≫ f.left = GlobalTheory.SplitTorus.bcMap p X ≫ g.left := by
    rw [← GlobalTheory.TorusPart.pullTorus_left h f, ← GlobalTheory.TorusPart.pullTorus_left h g, e]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k]
  · simp only [Over.pullback_map_left, pullback.lift_snd]

theorem spread₂_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  intro B H _ _ hH V₁ _ _ _ _ G₁ _ _ _ D₁ A₁ U₁ ξ₁ β₁ _ V₂ _ _ _ _ G₂ _ _ _ D₂ A₂ U₂ ξ₂ β₂ _ ρ hS
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hGW, hj, -, hc, -, -, -, -, hΩj, hκj⟩ := hS
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  haveI := hj
  let f : splitTorus (Sp W) F ⟶ GW := GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j
  have e0 : (1 : splitTorus (Sp W) F ⟶ GW) = GlobalTheory.SplitTorus.torusMap (Sp W) (0 : D₁.toPre.X →+ F) ≫ j := by
    rw [GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]

  have hκ : GlobalTheory.TorusPart.pullTorus hm f = GlobalTheory.TorusPart.pullTorus hm 1 := by
    rw [e0, GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hκj, ← Category.assoc,
      ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, hlρ,
      AddMonoidHom.zero_comp]
  letI : Algebra W κ := c.toAlgebra
  letI : Algebra (ResidueField W) κ := (ResidueField.lift c).toAlgebra
  haveI : IsScalarTower W (ResidueField W) κ :=
    IsScalarTower.of_algebraMap_eq' (ResidueField.lift_comp_residue c).symm
  have hbc : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange W κ).map 1 :=
    pullback_map_eq_of_pullTorus_eq hm f 1 hκ

  have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension W (ResidueField W) κ _ _ f 1 hbc
  have hsep : IsSeparated GW.hom :=
    (GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ψ H GW φW hGW hH).separated
  have hf1 : f = 1 := GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow W F GW hsep f 1 (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one W F GW f inferInstance hk)

  have hf0 : GlobalTheory.SplitTorus.torusMap (Sp W) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp W) 0 ≫ j := hf1.trans e0
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) hf0
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩj] at e2
  haveI := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₁.gt 0) hb₁ hn₁).1
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.Poinc.Sep.Spz
