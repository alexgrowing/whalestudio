import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem pull_inv_cls_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) :
    CechPic.pull (GrpObj.inv : G' ⟶ G').left (CechPic.cls L' hL') = CechPic.cls L' hL' ↔
      LBIso ((L.pull (GrpObj.inv : G ⟶ G).left).pull φ) (L.pull φ) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _),
    (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 e, CechPic.cls_pull hL, CechPic.cls_pull (pull_isLB hL _),
    CechPic.cls_pull hL, ← CechPic.pull_comp, ← CechPic.pull_comp, OddDescent.inv_left_comp h]

theorem exists_sym : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ e hs
  have := hG.proper
  obtain ⟨a, ha, H⟩ := exists_lbIso G.hom h.1 (pull_isLB hL _) hL
    ((pull_inv_cls_iff h hL hL₀ e).1 (OddDescent.pull_inv_cls_of_sym A hL₀ hs))
  exact ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' e' => OddDescent.sym_of_pull_inv_cls G' hL'
    ((pull_inv_cls_iff h' hL hL' e').2 (H R' g hg _ π G'.hom h'.1.w))⟩

end GlobalTheory.GenSpread
