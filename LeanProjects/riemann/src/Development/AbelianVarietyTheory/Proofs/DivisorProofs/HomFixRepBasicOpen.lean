import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixTransport

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X)
    (G' : Z ⟶ Y') (h : G ≫ F = G' ≫ F') : LBIso ((L.pull F).pull G) ((L.pull F').pull G') :=
  LBIso.chartPull
    (chartPullLinComb L F (fun _ : PUnit => G) (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)
    (chartPullLinComb L F' (fun _ : PUnit => G') (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => by rw [Category.id_comp, h])
    (lbIso_self (pull_isLB hL (G ≫ F)))

theorem lbIso_pull {X Y : Scheme.{0}} {L M : LB X} (H : LBIso L M) (h : Y ⟶ X) : LBIso (L.pull h) (M.pull h) :=
  LBIso.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl) H

theorem lbIso_congr {X : Scheme.{0}} {P P' Q Q' : LB X} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (hQ' : Q'.IsLB)
    (e₁ : LBIso P' P) (H : LBIso P Q) (e₂ : LBIso Q Q') : LBIso P' Q' :=
  LBIso.trans hP' hQ hQ' (LBIso.trans hP' hP hQ e₁ H) e₂

section Transport

variable {S S₁ S₂ : Scheme.{0}} (e : S₁ ≅ S₂) {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  (hL : L.IsLB) (hM : M.IsLB) {Af Bf : Over S₂} [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left)
  (φB : Bf.left ⟶ B.left)

def transport (R : HomFixRep Af Bf (L.pull φA) (M.pull φB)) :
    HomFixRep ((Over.pullback e.hom).obj Af) ((Over.pullback e.hom).obj Bf)
      (L.pull (pullback.fst Af.hom e.hom ≫ φA)) (M.pull (pullback.fst Bf.hom e.hom ≫ φB)) where
  H := R.H
  π := R.π ≫ e.inv
  AH := R.AH
  BH := R.BH
  φA := pullback.lift R.φA (R.AH.hom ≫ R.π ≫ e.inv) (by simp [R.pbA.1.w])
  φB := pullback.lift R.φB (R.BH.hom ≫ R.π ≫ e.inv) (by simp [R.pbB.1.w])
  pbA := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbA.congr (by simp) rfl)
  pbB := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbB.congr (by simp) rfl)
  Φ := R.Φ
  hom := R.hom
  iso := lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
    (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _ _ _ (by erw [pullback.lift_fst_assoc])) R.iso
    (lbIso_pull (lbIso_pull_pull hM _ _ _ _ (by erw [pullback.lift_fst_assoc])) _)
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB hΦ hI
    have hA₂ := hA.comp (isGrpPullback_pullback Af e.hom)
    have hB₂ := hB.comp (isGrpPullback_pullback Bf e.hom)
    obtain ⟨h, ⟨hπ, ψA, ψB, pA, pB, eA, eB, eΦ⟩, hu⟩ := R.rep T (t ≫ e.hom) A' B'
      (φA' ≫ pullback.fst Af.hom e.hom) (φB' ≫ pullback.fst Bf.hom e.hom) Φ' hA₂ hB₂ hΦ
      (lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
        (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
        (lbIso_pull_pull hL φA (φA' ≫ pullback.fst Af.hom e.hom) (pullback.fst Af.hom e.hom ≫ φA) φA' (by simp)) hI
        (lbIso_pull (lbIso_pull_pull hM (pullback.fst Bf.hom e.hom ≫ φB) φB' φB (φB' ≫ pullback.fst Bf.hom e.hom)
          (by simp)) Φ'.left))
    refine ⟨h, ⟨?_, ψA, ψB, pA, pB, ?_, ?_, eΦ⟩, ?_⟩
    · rw [← Category.assoc, hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eA
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pA.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hA.1.w.symm
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eB
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pB.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hB.1.w.symm
    · rintro h' ⟨hπ', ψA', ψB', pA', pB', eA', eB', eΦ'⟩
      refine hu h' ⟨by rw [← hπ']; simp, ψA', ψB', pA', pB', by rw [← eA', Category.assoc]; erw [pullback.lift_fst],
        by rw [← eB', Category.assoc]; erw [pullback.lift_fst], eΦ'⟩

end Transport

end GlobalTheory.HomFixTransport

open GlobalTheory.HomFixTransport in

theorem GlobalTheory.HomFixTransport.homFixRep_basicOpen : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (f : Rg), L.IsLB → M.IsLB → (∀ (Af Bf : Over (Sp (Localization.Away f))) [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left) (φB : Bf.left ⟶ B.left), IsGrpPullback Af A (spMap (algebraMap Rg (Localization.Away f))) φA → IsGrpPullback Bf B (spMap (algebraMap Rg (Localization.Away f))) φB → ∃ R : HomFixRep Af Bf (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∀ U : (Sp Rg).Opens, U = PrimeSpectrum.basicOpen f → ∃ (AU : Over U.toScheme) (_ : GrpObj AU) (BU : Over U.toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A U.ι φA ∧ IsGrpPullback BU B U.ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ A B _ _ L M f hL hM hyp U hU
  have hr : Set.range U.ι = Set.range (spMap (algebraMap Rg (Localization.Away f))) := by
    rw [Scheme.Opens.range_ι, hU]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  haveI : IsOpenImmersion (spMap (algebraMap Rg (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Rg (Localization.Away f)))))
  let e := IsOpenImmersion.isoOfRangeEq U.ι (spMap (algebraMap Rg (Localization.Away f))) hr
  have he : e.hom ≫ spMap (algebraMap Rg (Localization.Away f)) = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨R, h₁, h₂, h₃⟩ := hyp _ _ _ _ (isGrpPullback_pullback A (spMap (algebraMap Rg (Localization.Away f))))
    (isGrpPullback_pullback B (spMap (algebraMap Rg (Localization.Away f))))
  refine ⟨_, inferInstance, _, inferInstance, _, _,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback A _)).congr he rfl,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback B _)).congr he rfl,
    transport e hL hM _ _ R, ?_, ?_, ?_⟩
  · show QuasiCompact (R.π ≫ e.inv); infer_instance
  · show IsSeparated (R.π ≫ e.inv); infer_instance
  · show LocallyOfFiniteType (R.π ≫ e.inv); infer_instance
