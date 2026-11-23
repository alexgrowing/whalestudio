import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Mum

theorem exists_comp_eq_fst {S S' U U' X X' : Scheme.{0}} {g : X ⟶ S} {g' : X' ⟶ S'} {s : S' ⟶ S} {β : X' ⟶ X}
    (pb : IsPullback β g' g s) {j : U ⟶ S} [Mono j] {j' : U' ⟶ S'} {u : U' ⟶ U} (sq : u ≫ j = j' ≫ s)
    (κ : pullback g' j' ⟶ pullback g j) (hκ : κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    ∃ c : pullback (pullback.snd g j) u ⟶ pullback g' j', c ≫ κ = pullback.fst _ _ := by
  have w : (pullback.fst (pullback.snd g j) u ≫ pullback.fst g j) ≫ g = (pullback.snd (pullback.snd g j) u ≫ j') ≫ s := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, sq, Category.assoc]
  refine ⟨pullback.lift (pb.lift _ _ w) _ (pb.lift_snd _ _ w), ?_⟩
  rw [← cancel_mono (pullback.fst g j), Category.assoc, hκ, pullback.lift_fst_assoc, pb.lift_fst]

theorem lbIso_pull_pull_of_third {Q Y X Z Z' B : Scheme.{0}} {c : Q ⟶ Y} {κ : Y ⟶ X} {q : Q ⟶ X} (hc : c ≫ κ = q)
    {p : X ⟶ Z} {p' : Y ⟶ Z'} {β : Z' ⟶ Z} (hκ : κ ≫ p = p' ≫ β) {a : X ⟶ B} {M : LB B} {N : LB Z} {L' : LB Z'}
    (hM : M.IsLB) (hN : N.IsLB) (hL' : L'.IsLB) (h₁ : LBIso (L'.pull p') (M.pull (κ ≫ a))) (h₂ : LBIso L' (N.pull β)) :
    LBIso ((M.pull a).pull q) ((N.pull p).pull q) := by
  have hA := pull_isLB hM a
  have hP := pull_isLB hN p
  have e₁ : LBIso (L'.pull (c ≫ p')) (M.pull (q ≫ a)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp c rfl (by rw [← Category.assoc, hc]) h₁
  have e₂ : LBIso (L'.pull (c ≫ p')) (N.pull (q ≫ p)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso h₂ _ (by rw [Category.assoc, ← hκ, ← hc, Category.assoc])
  exact LBIso.trans (pull_isLB hA _) (pull_isLB hM _) (pull_isLB hP _)
    (GlobalTheory.GenSpread.lbIso_pull_pull hM q rfl).symm
    (LBIso.trans (pull_isLB hM _) (pull_isLB hL' _) (pull_isLB hP _) e₁.symm
      (LBIso.trans (pull_isLB hL' _) (pull_isLB hN _) (pull_isLB hP _) e₂
        (GlobalTheory.GenSpread.lbIso_pull_pull hN q rfl)))

theorem exists_fractionRing_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ g : FractionRing R →+* FractionRing R',
      g.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := by
  have hinj : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    fun a b h => hρ (IsFractionRing.injective R' (FractionRing R') h)
  exact ⟨IsFractionRing.lift (K := FractionRing R) hinj,
    RingHom.ext fun r => IsFractionRing.lift_algebraMap (K := FractionRing R) hinj r⟩

theorem lbIso_generic_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G' → IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → ∀ (L' : LB G'.left), L'.IsLB → LBIso (L'.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) → ∀ P : GlobalTheory.UU.CP G, LBIso L' (P.L.L.pull β) → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ G' _ _ G _ _ β _ _ pb A gen κ hgen hκ L' hL' h₁ P h₂
  obtain ⟨gam, hgam⟩ := exists_fractionRing_map ρ hρ.2.1
  have sq : spMap gam ≫ jK R = jK R' ≫ spMap ρ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap hgam).trans (spMap_comp ρ _))
  have hX : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback A.isAb (isGrpPullback_of_iso gen)
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  obtain ⟨c, hc⟩ := exists_comp_eq_fst pb.1 sq κ hκ
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap gam) _ hX (pull_isLB A.isLB _)
    (pull_isLB P.L.isLB _) (lbIso_pull_pull_of_third hc hκ A.isLB P.L.isLB hL' h₁ h₂)

end GlobalTheory.Mum
