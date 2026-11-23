import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.EighthPowerLocal

open GlobalTheory.SS GlobalTheory.CechPic GlobalTheory.MatrixBundle

theorem relAmple_diag_lam {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {B : Over (Sp R)} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hlam : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  let q := Out.powIsPowGrp B 2
  have hG : IsAbelianScheme (Out.powObj B 2) := (PowGrp.powers _ _ B 2 q).2.2.2.1 hB
  let ψ : B ⟶ Out.powObj B 2 := (Out.powIsLimit B 2).lift (Fan.mk B ![𝟙 B, (𝟙 B)⁻¹])
  have hψ : ∀ u, ψ ≫ q.pr u = ![𝟙 B, (𝟙 B)⁻¹] u := fun u => (Out.powIsLimit B 2).fac _ ⟨u⟩
  have hbox : (Out.boxLB M q.pr).IsLB := LB.isLB_linComb hM _ _
  have hfin : IsFinite ψ.left := by
    have := hB.proper
    have := hG.proper
    have : IsSeparated ((q.pr 0).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsSeparated (q.pr 0).left := IsSeparated.of_comp _ B.hom
    have : IsFinite (ψ.left ≫ (q.pr 0).left) := by
      rw [← Over.comp_left, hψ]
      exact inferInstanceAs (IsFinite (𝟙 B.left))
    exact IsFinite.of_comp _ (q.pr 0).left
  have hid : IsFinite (𝟙 B : B ⟶ B).left := inferInstanceAs (IsFinite (𝟙 B.left))
  have a₁ := (relAmple_finite_pow_iso _ B _ ψ _ 1 one_pos hB hG hbox hfin).1
    (relAmple_boxLB _ _ B 2 q M hM ha)
  refine (relAmple_finite_pow_iso _ B B (𝟙 B) _ 1 one_pos hB hB (pull_isLB hbox _) hid).2.2.2 _
    (pull_isLB hlam _) ((cls_eq_iff (pull_isLB hbox _) (pull_isLB hlam _)).1 ?_) a₁
  have h₀ : pull (1 : B ⟶ B).left (cls M hM) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls M hM))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := R) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls M hM) (fst B B) (snd B B) := cls_cube_two hM _ _ hlam
  have h₂ := lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  rw [cls_pull hbox, cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd, cls_linComb hM, map_sum, Fin.sum_univ_two,
    one_smul, one_smul, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, hψ, hψ]
  refine Eq.trans ?_ (eq_neg_of_add_eq_zero_left h₂.symm).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

open SiegelOfPolarised PrimNorm in

def siegOne (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (g : ℕ) :
    SiegPre g 1 ((1 : Rˣ) : R) (𝟙 (Sp R)) where
  A := B
  ab := hB
  P := abelian₂ B M
  isLB := LB.isLB_linComb hM _ _
  rig₁ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  symm := lbIso_lam_pull hM _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact EighthPowerFactor.weilIs_one_one hG hB (pull_isLB (LB.isLB_linComb hM _ _) _) _

end GlobalTheory.EighthPowerLocal

end
