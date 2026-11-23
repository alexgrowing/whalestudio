import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_zero_hom_isIso {X : Scheme.{0}} (A : Over X) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let t : Over.mk (𝟙 X) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let u : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 X) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have h1 : u ≫ t = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨t.left, ?_, ?_⟩⟩
  · have h2 := congrArg Over.Hom.left h1
    simpa [u] using h2
  · simpa using Over.w t

private noncomputable def tailMap {X : Scheme.{0}} (A : Over X) (k : ℕ) : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
  Pi.lift fun j => GlobalTheory.KS.pr A j.succ

private theorem tailMap_pr {X : Scheme.{0}} (A : Over X) (k : ℕ) (j : Fin k) :
    tailMap A k ≫ GlobalTheory.KS.pr A j = GlobalTheory.KS.pr A j.succ := by
  simp [tailMap, GlobalTheory.KS.pr]

set_option maxHeartbeats 400000 in
private theorem pow_succ_isPullback {X : Scheme.{0}} (A : Over X) (k : ℕ) :
    IsPullback (GlobalTheory.KS.pr A (0 : Fin (k + 1))).left (tailMap A k).left A.hom (GlobalTheory.KS.pow A k).hom := by
  refine Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk (GlobalTheory.KS.pr A (0 : Fin (k + 1))) (tailMap A k)) ?_
  refine BinaryFan.IsLimit.mk _ (fun f g => Pi.lift (Fin.cases f (fun j => g ≫ GlobalTheory.KS.pr A j))) ?_ ?_ ?_
  · intro T f g
    simp [GlobalTheory.KS.pr]
  · intro T f g
    refine Pi.hom_ext _ _ fun j => ?_
    simp [tailMap, GlobalTheory.KS.pr]
  · intro T f g m h1 h2
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h1 h2
    refine Pi.hom_ext (f := fun _ : Fin (k + 1) => A) (m : T ⟶ ∏ᶜ fun _ : Fin (k + 1) => A) _ fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [← h1, GlobalTheory.KS.pr]
    · rw [← h2]
      simp [tailMap, GlobalTheory.KS.pr]

theorem UpperTheory.Gal.W2.holPi_of :
    UpperTheory.Gal.W2.HolPi := by
  intro V _ _ X A k
  induction k with
  | zero =>
    intro B s hB h0 _
    haveI := pow_zero_hom_isIso A
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h0 (inv (GlobalTheory.KS.pow A 0).hom)) ?_
    intro b _
    simp
  | succ k ih =>
    intro B s hB h0 hj
    refine GlobalTheory.HolPullback.isHolTo_of_components V B _ _ _ _ _ _ _ _ s (pow_succ_isPullback A k) hB (hj 0) ?_
    apply ih B (fun v => s v ≫ (tailMap A k).left) hB
    · refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr h0 ?_
      intro b _
      simp only [Category.assoc, Over.w]
    · intro j
      refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr (hj j.succ) ?_
      intro b _
      simp only [Category.assoc]
      rw [← Over.comp_left, tailMap_pr]
