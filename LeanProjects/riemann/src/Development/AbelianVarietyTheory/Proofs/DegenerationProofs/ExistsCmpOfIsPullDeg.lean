import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourthSide
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPreUSetPsi
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPsiGeneratingOnWholeSpectrumStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCubicalBundleMapOfPulledBackDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCubeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreBaseChange

theorem exists_cmp_of_isPullDeg (hG : GlobalFnsSt) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I') {D : DegPre R} {D₁ D' : DegPre V}
    (hD : IsPullDeg φ D D₁) {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing V))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left)
    (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F))
    (hw : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL) :
    ∃ (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  obtain ⟨bc, hbc, rfl⟩ := grpPullback_iso pb (isGrpPullback_pullback G (specOf φ))
  choose h q' i' hh hq' using fun e => gtCoord_baseChange_maps R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e)
  choose g _ hg using fun e => exists_gtCoord_pull hG R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e) (h e) (q' e)
    (i' e) (hh e) (hq' e)
  have hc := fun e => gtCoord_compat_of_pull R V φ D D₁ hD I I' G G' _ e (U.gt e) (U.gt (e + 1)) (g e) (g (e + 1))
    (h e) (h (e + 1)) (hh e) (hh (e + 1)) (hg e) (hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w w_gen sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.P.L D₁.P.L U.P.L.L U'.P.L.L D.P.isLB
    D₁.P.isLB U.P.L.isLB U'.P.L.isLB _ _ (U.gt e).pG.left (g e).pG.left (fstG I e G).left (fstG I' e G').left (h e)
    (hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hw.gen (U.w_gen e)
  have pt : ∀ {Z X Y : Scheme.{0}} {a b : X ⟶ Y} (_ : a = b) (x : Z ⟶ X) (z : Z) {W : Y.Opens},
      a (x z) ∈ W → b (x z) ∈ W := fun e _ _ _ k => e ▸ k
  have compat : ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj V I' e G').left) (z : Z) (j : D₁.P.L.ι)
      (k : U'.P.L.L.ι), (g e).pG.left (x z) ∈ D₁.P.L.U j → (fstG I' e G').left (x z) ∈ U'.P.L.L.U k →
      gw (w (e + 1)) (x ≫ thickMap V I' e G') z j (fun _ => k) = gw (w e) x z j (fun _ => k) := by
    intro e Z x z j k hj hk
    have := Cmp.mono_fstG I (e + 1) G
    have t := LevelCompat.thickMap_fstG I e G
    have t' := LevelCompat.thickMap_fstG I' e G'
    have hm : thickMap V I' e G' ≫ h (e + 1) = h e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, hh (e + 1), ← Category.assoc, t', Category.assoc, t,
        hh e]
    obtain ⟨jM, hM⟩ := exists_chart D.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((g e).pG.left (x z)))
    obtain ⟨jL, hL⟩ := exists_chart U.P.L.isLB
      ((bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ((fstG I' e G').left (x z)))
    have a₀ := sq e Z x z jM j jL k hM hj hL hk
    have a₁ := sq (e + 1) Z (x ≫ thickMap V I' e G') z jM j jL k
      (pt (congrArg (· ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (hc e).1).symm x z hM)
      (pt (hc e).1.symm x z hj)
      (pt (congrArg (· ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)) t').symm x z hL) (pt t'.symm x z hk)
    have b := U.w_compat e Z (x ≫ h e) z jM jL (pt (hg e).1 x z hM) (pt (hh e).symm x z hL)
    rw [Category.assoc x, Category.assoc x, Category.assoc x, (hc e).1, t', hm, ← Category.assoc x (h e), b] at a₁
    exact mul_left_cancel (a₁.trans a₀.symm)
  refine ⟨⟨U'.semi, U'.gen, U'.gen_hom, U'.P, U'.wA, U'.wA_gen, g, fun e => (hc e).1, fun e => (hc e).2, w, w_gen,
      fun e => GlobalTheory.T.fourthSide_respects_rig_symmetry_cube hG R V I I' φ hI D D₁ A G G' U U'.P _ _ wL hw _ _ hD.w (GlobalTheory.T.isCubicalBundleMap_of_pulled_back_degeneration hG R V φ D D₁ hD) e
        (g e) (h e) (hh e) (hg e).1 (w e) (sq e), compat⟩,
    ⟨pb, wL, hw, _, pull_grp hD, hD.w, hD.w_gen, hD.xe, hD.c_pr, fun e Z x' x hx => ?_, hI⟩, rfl, HEq.rfl⟩
  have := Cmp.mono_fstG I e G
  obtain rfl : x = x' ≫ h e := (cancel_mono (fstG I e G).left).1 (hx.trans (by rw [Category.assoc, hh e]))
  refine ⟨(congrArg (x' ≫ ·) (hg e).1).trans (Category.assoc _ _ _).symm,
    fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
  · refine (CubTransport.val_pmaps ((hg e).2 χ).1 ((hg e).2 χ).2 x' hJ hJ').trans
      ((mul_comm _ _).trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_)))
    rw [Category.assoc]
  · exact sq e Z x' z _ _ k k' (pt (hg e).1.symm x' z (hJ ((x' ≫ h e) ≫ (U.gt e).pG.left)))
      (hJ' (x' ≫ (g e).pG.left)) (pt (hh e) x' z hk) hk'

theorem exists_cmp_pull : Laws → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ (D₁ : DegPre V) (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  intro hL R V _ _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨ψ, h, hW⟩ := GlobalTheory.T.exists_psi_generating_on_whole_spectrum R D
  obtain ⟨D₁, hD, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R V φ (setPsi D ψ h) ⊤ hW trivial
  obtain ⟨U₁, C, h₁, h₂⟩ := exists_cmp_of_isPullDeg hL.globalFns hI hD (U.setPsi ψ h) U' F pb wL hw
  exact ⟨D₁, U₁, ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩, h₁, h₂⟩

end GlobalTheory.LN.PreBaseChange
end
