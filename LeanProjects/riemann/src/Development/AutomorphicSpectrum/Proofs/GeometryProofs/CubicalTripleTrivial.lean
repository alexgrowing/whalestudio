import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqSingleOfIsUnitCoeff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.CubeUnit

open GlobalTheory.CubicUnit

theorem eq_one_at_rational_points : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  intro K _ G _ _ hs τ v hv x₀ y₀ w₀
  letI := τ.addCommGroup
  haveI := τ.free
  letI := τ.grpB
  haveI := τ.q_hom
  haveI := τ.i_hom
  haveI := τ.q_flat
  haveI := τ.q_surjective
  haveI := τ.q_quasiCompact
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI hGc : ConnectedSpace G.left := (GlobalTheory.GroupConn.connectedSpace_group (Sp K) G).1
  haveI hYc : ConnectedSpace (G ⊗ G).left := GlobalTheory.GroupConn.connectedSpace_tensor G G
  haveI hsn : Smooth (snd G G).left := by
    show Smooth (pullback.snd G.hom G.hom)
    infer_instance
  haveI hsm : Smooth (G ⊗ G).hom := by
    rw [← Over.w (snd G G)]
    infer_instance
  haveI hYr : IsReduced (G ⊗ G).left := GlobalTheory.isReduced_of_smooth_of_isReduced (G ⊗ G).hom
  have hf1 : ∀ (T : Over (Sp K)) (x y : T ⟶ G), ev (lift (1 : T ⟶ G) (lift x y)) v = 1 :=
    fun T x y => Units.ext (hv T x y).1
  have hf2 : ∀ (T : Over (Sp K)) (x y : T ⟶ G), ev (lift x (lift (1 : T ⟶ G) y)) v = 1 :=
    fun T x y => Units.ext (hv T x y).2.1
  let m : splitTorus (Sp K) τ.X ⊗ (G ⊗ G) ⟶ G ⊗ (G ⊗ G) :=
    lift ((fst _ _ ≫ τ.i) * (snd _ _ ≫ fst _ _)) (lift (snd _ _ ≫ snd _ _) (toUnit _ ≫ w₀))
  have hm : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      lift t (lift x y) ≫ m = lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀)) := fun Z t x y => by
    simp [m, comp_lift, MonObj.comp_mul]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul (Sp K) τ.X (G ⊗ G) (ev m v)
  have h1 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      ev (lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀))) v =
        chV t χ * ev (lift x (lift y (toUnit Z ≫ w₀))) v := fun Z t x y => by
    have e : ev (lift t (lift x y)) (ev m v) =
        chV t χ * ev (lift (1 : Z ⟶ splitTorus (Sp K) τ.X) (lift x y)) (ev m v) :=
      Units.ext (hχ Z t (lift x y))
    rw [ev_comp, ev_comp, hm, hm, MonObj.one_comp, _root_.one_mul] at e
    exact e
  have h2 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X), chV t χ = 1 := fun Z t => by
    have e := h1 Z t 1 1
    rw [hf2, hf2, _root_.mul_one] at e
    exact e.symm
  have h3 : ∀ (Z : Over (Sp K)) (t : Z ⟶ splitTorus (Sp K) τ.X) (x y : Z ⟶ G),
      ev (lift ((t ≫ τ.i) * x) (lift y (toUnit Z ≫ w₀))) v =
        ev (lift x (lift y (toUnit Z ≫ w₀))) v := fun Z t x y => by
    rw [h1, h2, _root_.one_mul]
  let s : G ⟶ G ⊗ (G ⊗ G) := lift (𝟙 G) (lift (toUnit G ≫ y₀) (toUnit G ≫ w₀))
  have hs' : ∀ (Z : Over (Sp K)) (g : Z ⟶ G),
      g ≫ s = lift g (lift (toUnit Z ≫ y₀) (toUnit Z ≫ w₀)) := fun Z g => by
    simp [s, comp_lift]
  have h8 : IsWt τ.i ⊤ (ev s v).val 0 := isWt_top_iff.2 fun Z t g => by
    rw [← ev_val, ← ev_val, ev_comp, ev_comp, hs', hs', h3, chV_zero, Units.val_one, _root_.one_mul]
  obtain ⟨c, hc⟩ := (invariant_functions_descend (Sp K) G τ.B _ τ.q τ.i τ.q_hom τ.i_hom τ.q_flat
    τ.q_surjective τ.q_quasiCompact τ.isKernel ⊤).2.2 (ev s v).val fun Z t g h₁ h₂ => by
      refine (h8 Z t g h₁ h₂).trans ?_
      rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul]
      rfl
  obtain ⟨d, hd⟩ := (GlobalTheory.globalFns_holds (Sp K) τ.B τ.isAbelian).2 c
  have hud : (ev s v).val = G.hom.appTop.hom d := by
    rw [← Over.w τ.q, FunDescent.comp_appTop_apply, hd]
    exact hc.symm
  have hd1 : d = 1 := by
    have e : ev (1 : 𝟙_ (Over (Sp K)) ⟶ G) (ev s v) = 1 := by
      rw [ev_comp, hs', toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp]
      exact hf1 _ y₀ w₀
    have e := congrArg Units.val e
    rw [ev_val, hud, ← FunDescent.comp_appTop_apply, Over.w] at e
    simpa using e
  have hu : ev s v = 1 := by
    apply Units.ext
    rw [hud, hd1, map_one, Units.val_one]
  have e : ev x₀ (ev s v) = 1 := by
    rw [hu]
    exact map_one _
  rw [ev_comp, hs', toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at e
  exact congrArg Units.val e

end GlobalTheory.CompanionTheory.Ar.CubeUnit
end
