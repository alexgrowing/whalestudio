import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThPull
open GlobalTheory.ThetaPtMove

theorem thG_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)} {y : T ⟶ G} {c : Γ(T.left, ⊤)}
    (H : ThG G L ρ m θ y c) : ThG G L ρ m (VVRank.pullS G _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS G _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec G ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec G t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'

theorem thList_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  intro S G _ _ L ρ hL hρ m N K K' _ _ i x θ pt c H
  let β : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hβ : β.left = spMap i := Over.homMk_left _ _
  refine ⟨fun a => β ≫ pt a, fun a => by simp only [Over.comp_left, hβ], fun a b h => H.1 (TorsionFieldExt.comp_injective β _ h), fun a => ?_,
    fun F _ _ k => ?_⟩
  · have q := thG_pull hL hρ β (H.2.1 a)
    have e : β.left.appTop.hom (GlobalTheory.ZH.fn (c a)) = GlobalTheory.ZH.fn (i (c a)) :=
      (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
    rw [e] at q
    exact q
  · have e : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
    rw [e]
    intro p hp
    obtain ⟨a, ha⟩ := H.2.2 F (k.comp i) p hp
    refine ⟨a, ?_⟩
    rw [ha, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Over.comp_left, hβ, Category.assoc]

end GlobalTheory.UMin.ThPull
