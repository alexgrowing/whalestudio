import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullUnif

theorem coordMap_of_isPullDeg {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {g : R →+* V} {D : DegPre R} {D' : DegPre V} (hD : IsPullDeg g D D') :
    CoordMap D D' g hD.xe.symm.toAddMonoidHom := by
  intro y r r' hr hr'
  have hr2 : PsiCoord D (hD.xe (hD.xe.symm y)) r := by rwa [AddEquiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr2
  have h1 : Associated (u * g r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  exact Associated.trans ⟨u, mul_comm _ _⟩ h1

set_option maxHeartbeats 1600000 in

theorem gtTorus_pull {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    {U : Unif (maximalIdeal R) D A G} {U' : Unif (maximalIdeal V) D' A' G'} {g : R →+* V}
    {bc : G' ≅ (Over.pullback (specOf g)).obj G} {hD : IsPullDeg g D.toPre D'.toPre}
    (H : IsPullUnif g hD bc U U')
    {κ : Type} [Field κ] {b : V →+* κ} (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), (b.comp g) x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ' : G₀.left ⟶ G'.left}
    (hp' : IsGrpPullback G₀ G' (spMap b) φ')
    (hp : IsGrpPullback G₀ G (spMap (b.comp g)) (φ' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g))) :
    GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hp' =
      GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb' hp := by
  obtain ⟨wL, -, he, -, Hs⟩ := (isPullUnif_iff_stalks R V _ _ g D D' hD A A' G G' bc U U').1 H
  obtain ⟨h, hf, ⟨hpG, hψ⟩, -⟩ := Hs 0
  obtain ⟨s, τ, hτ⟩ := GlobalTheory.PullLinear.exists_point (U.gt 0) (U'.gt 0) hpG (hψ 0).1 (𝟙 _)
  have : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have C1 : GlobalTheory.TorusPart.thickLift hb' hp = GlobalTheory.TorusPart.thickLift hb hp' ≫ h := by
    rw [← cancel_mono (pullback.fst G.hom (thick R (maximalIdeal R) 0)), GlobalTheory.TorusPart.thickLift_fst,
      Category.assoc]
    erw [hf]
    erw [← Category.assoc (GlobalTheory.TorusPart.thickLift hb hp'), GlobalTheory.TorusPart.thickLift_fst hb hp']
  have hτ' : (U'.gt 0).i.left ≫ h = τ.left ≫ (U.gt 0).i.left := by
    rw [← Over.comp_left, hτ, Category.id_comp]
  have key : GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left =
      (GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X := by
    have wA : (GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, ← Over.w (U.gt 0).i, ← Category.assoc τ.left, ← hτ', Category.assoc,
        ← Category.assoc _ (U'.gt 0).i.left]
      erw [← GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
      rw [Category.assoc, ← Category.assoc _ h, ← C1, (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp).1.w,
        ← Category.assoc, Over.w]
    have wB : ((GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w]
    have hchar : ∀ x' : D'.toPre.X, τ.left.appTop.hom (Rosenlicht.chi D.toPre.X (hD.xe x')) =
        Rosenlicht.chi D'.toPre.X x' := by
      intro x'
      apply TopCat.Presheaf.section_ext (splitTorus _ D'.toPre.X).left.sheaf ⊤
      intro z hz
      have e := congrArg Units.val
        (GlobalTheory.PullLinear.char_eq (U.gt 0) (U'.gt 0) hD.w (hψ x').1 (hψ x').2 (𝟙 _) τ hτ z)
      rw [gm_val τ.left z ⊤ trivial, gm_val (Over.Hom.left (𝟙 (WeightPf.Te D'.toPre (maximalIdeal V) 0))) z ⊤ trivial, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val] at e
      exact e
    have e := GlobalTheory.SplitTorus.hom_ext (T := Over.mk ((splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb'))
      (g := Over.homMk _ wA) (g' := Over.homMk _ wB) (fun a => by
        rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq]
        simp only [Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        rw [GlobalTheory.SplitTorus.bcMap_appTop_chi, GlobalTheory.SplitTorus.torusMap_appTop_chi,
          ← AddEquiv.apply_symm_apply hD.xe a, hchar, GlobalTheory.SplitTorus.bcMap_appTop_chi,
          AddEquiv.apply_symm_apply]
        rfl)
    exact congrArg (·.left) e
  apply GlobalTheory.TorusPart.hom_ext_of_pullback (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp)
  rw [Over.comp_left, Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp) (U.gt 0).i]
  rw [C1, ← Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
  rw [Category.assoc, hτ', ← Category.assoc, key, Category.assoc]

set_option maxHeartbeats 800000 in

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsLocalHom g → ∀ (bc : G' ≅ (Over.pullback (specOf g)).obj G), IsMonHom bc.hom → β = bc.hom.left ≫ pullback.fst G.hom (specOf g) → ∀ hD : IsPullDeg g D.toPre D'.toPre, IsPullUnif g hD bc U U' → LBIso U'.LG.L (U.LG.L.pull β) ∧ CoordMap D.toPre D'.toPre g hD.xe.symm.toAddMonoidHom ∧ EquivMap U U' β hD.xe.symm.toAddMonoidHom := by
  intro R _ _ _ _ G _ _ _ D A U V _ _ _ _ G' _ _ _ D' A' U' g β hloc bc hbc hβ hD H
  subst hβ
  refine ⟨?_, coordMap_of_isPullDeg hD, ?_⟩
  · obtain ⟨wL, hwL, -⟩ := H.lg
    exact ⟨wL, hwL⟩
  intro f f' _ _ hcomm m m' hm hm' y
  have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), residue V x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), ((residue V).comp g) x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 ((map_mem_nonunits_iff g x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx))
  have hp' := isGrpPullback_pullback G' (spMap (residue V))
  have hβ : IsGrpPullback G' G (spMap g) (bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf g))).congr (Category.id_comp _) rfl
  have hp : IsGrpPullback ((Over.pullback (spMap (residue V))).obj G') G (spMap ((residue V).comp g))
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    (hp'.comp hβ).congr (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (residue V))).symm rfl
  have e' : ((Over.pullback (spMap (residue V))).map f').left ≫ pullback.fst G'.hom (spMap (residue V)) =
      pullback.fst G'.hom (spMap (residue V)) ≫ f'.left := pullback.lift_fst _ _ _
  have e : ((Over.pullback (spMap (residue V))).map f').left ≫
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) =
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) ≫ f.left := by
    rw [← Category.assoc, e', Category.assoc, hcomm]
    simp only [Category.assoc]
  have k' := hm' _ _ hb _ _ hp' _ e'
  have k := hm _ _ hb' _ _ hp _ e
  have K := gtTorus_pull H hb hb' hp' hp
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hb' hp).1
  have k2 := (Category.assoc _ _ _).trans ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V))
    hD.xe.symm.toAddMonoidHom ≫ ·) k.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Over.pullback (spMap (residue V))).map f') K.symm).trans (k'.trans
    ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) m' ≫ ·) K).trans (Category.assoc _ _ _).symm)))))
  have k3 := (cancel_mono _).1 k2
  rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at k3
  exact congrArg (fun φ : D.toPre.X →+ D'.toPre.X => φ y) (GlobalTheory.SplitTorus.torusMap_injective k3)

end GlobalTheory.Poinc.Eq8.PullUnif
