import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenAbelianSchemeRelAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescendsFiniteFlatSurjeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMumfordBundleQuotientStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualQuot

theorem exists_quotient_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), Good g B.hom ∧ FinAff B.left ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) ∧ (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) := by
  intro R _ _ A _ g hA hg L hL hamp
  obtain ⟨H, _, i, hi, hmono, hHf, hHfl, hrep⟩ := GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme R A hA L hL hamp
  obtain ⟨B, _, q, π, hB, hq, hqf, hqfl, hqs, hπ, hpb⟩ := GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup R A H i hA hi hmono hHf hHfl
  obtain ⟨P₀, hP₀, hform⟩ := GlobalTheory.T.exists_descent_mumfordBundle_quotient R A hA L hL H i hi hmono hHf hHfl hrep B q hB hq hqf hqfl hqs hpb
  have hc := hA.comm
  let c : A ⊗ B ⟶ A ⊗ B := snd A B ≫ lift (1 : B ⟶ A) (𝟙 B)
  let P : LB (A ⊗ B).left := tens P₀ (dual (P₀.pull c.left))
  have hP : P.IsLB := isLB_tens hP₀ (isLB_dual (pull_isLB hP₀ _))
  have hcls : cls P hP = cls P₀ hP₀ - GlobalTheory.CechPic.pull c.left (cls P₀ hP₀) := by
    rw [cls_tens hP₀ (isLB_dual (pull_isLB hP₀ _)), cls_dual (pull_isLB hP₀ _), cls_pull hP₀, sub_eq_add_neg]
  have hev : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc hP₀ a t - evc hP₀ 1 t := by
    intro Y a t
    have e : lift a t ≫ c = lift (1 : Y ⟶ A) t := by
      simp only [c, lift_snd_assoc, comp_lift, MonObj.comp_one, Category.comp_id, lift_snd]
    simp only [evc]
    rw [hcls, map_sub, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, e]
  have hform' : ∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
    intro Y a x
    rw [hev, hform, hform, _root_.one_mul]
    abel
  have h0l : Triv (ev P (1 : B ⟶ A) (𝟙 B)) := by
    rw [triv_ev_iff hP, hev, sub_self]
  have h0r : Triv (ev P (𝟙 A) (1 : A ⟶ B)) := by
    have e : (1 : A ⟶ B) = (1 : A ⟶ A) ≫ q := (MonObj.one_comp q).symm
    rw [triv_ev_iff hP, e, hform', _root_.mul_one]
    abel
  have hadd : IsAdditive P := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hB hP h0l h0r
  have hBsm := hB.smooth
  have hAfa := GlobalTheory.T.finiteSetsInAffineOpen_abelianScheme_relAmple R A hA L hL hamp
  refine ⟨B, P, q, ⟨hP, hadd⟩, ⟨hB.proper, GlobalTheory.T.smoothOfRelativeDimension_descends_finite_flat_surjective _ A B g q hg hBsm hqf hqfl hqs, hB.geomConnected⟩, ?_, hqf, hqfl, hqs, hform', ?_⟩
  · intro F
    classical
    obtain ⟨U, hU, hF⟩ := hAfa (F.image π.left)
    exact ⟨π.left ⁻¹ᵁ U, hU.preimage π.left, fun x hx ↦ hF _ (Finset.mem_image_of_mem _ hx)⟩
  · intro Y x y
    constructor
    · intro h
      refine (hrep Y (x * y⁻¹)).2 ⟨hpb.lift x y h ≫ fst H A, ?_⟩
      have h1 := hpb.lift_fst x y h
      rw [comp_mul, hpb.lift_snd] at h1
      rw [eq_mul_inv_iff_mul_eq, Category.assoc, h1]
    · intro h
      obtain ⟨z, hz⟩ := (hrep Y (x * y⁻¹)).1 h
      have hx : x = lift z y ≫ ((fst H A ≫ i) * snd H A) := by
        rw [comp_mul, lift_fst_assoc, lift_snd, hz, inv_mul_cancel_right]
      rw [hx, Category.assoc, hpb.w, lift_snd_assoc]

end GlobalTheory.DualQuot
