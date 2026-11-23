import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelGaloisDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem eta_lift_one_id (A : Over S) [GrpObj A] : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = η[A ⊗ A] := by
  ext <;> simp [Hom.one_def]

theorem eta_lift_id_one (A : Over S) [GrpObj A] : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = η[A ⊗ A] := by
  ext <;> simp [Hom.one_def]

theorem eta_swap (A : Over S) [GrpObj A] : η[A ⊗ A] ≫ lift (snd A A) (fst A A) = η[A ⊗ A] := by
  ext <;> simp

theorem eq_zero_of_cart (hG : Out.GlobalFnsSt) {S' : Scheme.{0}} (π : S' ⟶ S) [Flat π] [Surjective π]
    [QuasiCompact π] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {B : Over S'} {φ : B.left ⟶ A.left}
    (hp : IsPullback φ B.hom A.hom π) (c : Pic A.left) (h₀ : pull (eSec A) c = 0) (h₁ : pull φ c = 0) : c = 0 := by
  refine TripleDescent.eq_zero_of_pull hG π hA c h₀ ?_
  have e : (TripleDescent.fibreProj A π).left = hp.isoPullback.inv ≫ φ := by
    simp [TripleDescent.fibreProj]
  rw [e, pull_comp, h₁, map_zero]

end GlobalTheory.SiegelGaloisDescent

namespace GlobalTheory

open SiegelDescent SiegelGaloisDescent CechPic

theorem exists_siegPre_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  intro h M o _ ζ X Y π s sY Ga _ ρ c A₀ _ φ φ₂ P₀ lev₀ hs hGal ab hp sq hP₀ hw ht hlev
  haveI := ab.comm
  have gf : Out.GlobalFnsSt := abelianSchemeLaws_all.1.globalFns
  haveI : IsFinite π := hGal.fin
  haveI : Etale π := hGal.etale
  haveI : Surjective π := hGal.onto
  haveI : Epi π := Flat.epi_of_flat_of_surjective π
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ π := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have ab₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ ab ab
  have hp₂ := isPullback_square hp.1 φ₂ sq
  have clsP : cls c.P c.isLB = pull φ₂ (cls P₀ hP₀) := by
    rw [← cls_pull hP₀ φ₂ (pull_isLB hP₀ _)]
    exact (cls_eq_iff _ _).2 hw
  have P₀e : pull (eSec (G2 A₀)) (cls P₀ hP₀) = 0 := by
    rw [← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact (cls_eq_zero_iff _).2 ht
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      η[A₀] ≫ a₀ = η[A₀ ⊗ A₀] → (∃ t : (c.P.pull a.left).Gen, t.IsGen) →
      ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := by
    intro a a₀ e e₀ hta
    have e₀' : eSec A₀ ≫ a₀.left = eSec (G2 A₀) := congrArg (fun q => q.left) e₀
    refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀ _ (pull_isLB hP₀ _)]
    refine eq_zero_of_cart gf π ab hp.1 _ ?_ ?_
    · rw [← pull_comp, e₀', P₀e]
    · rw [← pull_comp, ← e, pull_comp, ← clsP, ← cls_pull c.isLB _ (pull_isLB c.isLB _)]
      exact (cls_eq_zero_iff _).2 hta
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have esw : eSec (G2 A₀) ≫ (lift (snd A₀ A₀) (fst A₀ A₀)).left = eSec (G2 A₀) :=
      congrArg (fun q => q.left) (eta_swap A₀)
    have swsq := lift_square sq sq.2.symm sq.1.symm
    refine (cls_eq_iff hP₀ (pull_isLB hP₀ _)).1 (sub_eq_zero.1 (eq_zero_of_cart gf π ab₂ hp₂ _ ?_ ?_))
    · rw [map_sub, cls_pull hP₀ _ (pull_isLB hP₀ _), ← pull_comp, esw, P₀e, sub_zero]
    · rw [map_sub, cls_pull hP₀ _ (pull_isLB hP₀ _), ← pull_comp, ← swsq, pull_comp, ← clsP,
        ← cls_pull c.isLB _ (pull_isLB c.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c.symm
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρl, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) π
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρlev : ∀ a, ρl (lev₀ a) = c.lev a := fun a => (hρ _ _).2 (hlev a)
  have ρinj : Function.Injective ρl := fun x y e =>
    Over.OverMorphism.ext ((cancel_epi π).1 (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) (eta_lift_one_id A₀) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) (eta_lift_id_one A₀) c.rig₂
            symm := symm, lev := lev₀
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev⟩
  intro k _ _ x β z hx hz
  obtain ⟨y, hy⟩ := exists_lift_pt π x
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A π φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
