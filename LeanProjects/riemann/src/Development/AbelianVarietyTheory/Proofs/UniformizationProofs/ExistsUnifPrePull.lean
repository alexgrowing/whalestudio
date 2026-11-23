import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourthSide
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_unifPre_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (eA : (Over.pullback (jK R')).obj G' ≅ A'.A), IsMonHom eA.hom → (∃ wA : LB.Iso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen) → ∀ (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∃ (U' : UnifPre I' D' A' G') (wL' : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))), U'.LG = L' ∧ U'.gen = eA ∧ HEq wL' wL ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL' (r ≫ (fstG I' e G').left) z jL jL') := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc hI hbc U eA heA hA L' wL he hwL hrig
  have hgp : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  obtain ⟨c', s', hs', hsr, Hc, Hs⟩ := cubical_symmetry_transport _ _ (specOf φ) G G' _ hgp U.LG L' wL he hwL hrig
    U.cubG U.symG U.symG_gen U.symG_rig
  choose h q' i' hh H using fun e => gtCoord_baseChange_maps R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
  choose gt' _ Hg using fun e => exists_gtCoord_pull hG R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
    (h e) (q' e) (i' e) (hh e) (H e)
  have C := fun e => gtCoord_compat_of_pull R R' φ D.toPre D'.toPre hD I I' G G' _ e (U.gt e) (U.gt (e + 1))
    (gt' e) (gt' (e + 1)) (h e) (h (e + 1)) (hh e) (hh (e + 1)) (Hg e) (Hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w' hw' sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.toPre.P.L D'.toPre.P.L U.LG.L L'.L
    D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB L'.isLB _ _ (U.gt e).pG.left (gt' e).pG.left (fstG I e G).left
    (fstG I' e G').left (h e) (Hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hwL (U.w_gen e)
  have RC := unifPull_rig_compat R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩)
  have Ev := pulled_comparison_even hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) s' hs' Hs
  have Cu := w_cub_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) hgp c' Hc
  have ext : LBIso (A'.L.pull eA.hom.left) (L'.L.pull (pullback.fst G'.hom (jK R'))) :=
    LBIso.trans (pull_isLB A'.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB L'.isLB _) hA
      (LBIso.symm (LBIso.chartPull
        (chartPullPull L'.L _ _ rfl) (chartPullSame U.LG.L _ _ _ (pullback.fst G'.hom (jK R')) fun _ => rfl) ⟨wL, hwL⟩))
  exact ⟨{ smooth := MorphismProperty.of_isPullback hgp.1 U.smooth
           separated := MorphismProperty.of_isPullback hgp.1 U.separated
           gen := eA, gen_hom := heA, LG := L', cubG := c', symG := s', symG_gen := hs', symG_rig := hsr
           ext := ext, gt := gt', gt_q := fun e => (C e).1, gt_t := fun e => (C e).2
           w := w', w_gen := hw', w_rig := RC.1, w_even := Ev, w_cub := Cu, w_compat := RC.2 },
    wL, rfl, rfl, HEq.rfl, fun e => ⟨h e, hh e, Hg e, sq e⟩⟩

end GlobalTheory
