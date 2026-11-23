import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimUniqueOfIsoGrp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectDual

theorem mono_of_isPerfect {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    [IsMonHom x] (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem isIso_of_isEmpty {S : Scheme.{0}} (hS : IsEmpty S) {X Y : Over S} (f : X ⟶ Y) : IsIso f := by
  haveI : IsEmpty X.left := ⟨fun p ↦ hS.false (X.hom p)⟩
  haveI : IsEmpty Y.left := ⟨fun p ↦ hS.false (Y.hom p)⟩
  haveI : IsIso f.left := ⟨⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩⟩
  haveI : IsIso ((Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget S)

theorem isDual_of_isPerfect_of_additive (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) (haddA : IsAdditive P) (haddB : IsAdditive (swap P)) :
    IsDual A B P := by
  obtain ⟨B', _, P', hB', hd', h1, h2⟩ := hD S A hA
  obtain ⟨A'', _, Q, hA'', hdQ, k1, k2⟩ := hD S B hB
  obtain ⟨x, hx, -⟩ := h1.univ B P hP.isLB haddA
  have hs : (swap P).IsLB := pull_isLB hP.isLB _
  obtain ⟨y, hy, -⟩ := k1.univ A (swap P) hs haddB
  have hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying S A B B' P P' h1 h2.additive hP.isLB haddB x hx
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  have haddSS : IsAdditive (swap (swap P)) := (isAdditive_iff hss).2 fun Y a a' t ↦ by
    rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP.isLB hs, evc_swap hP.isLB hs,
      evc_swap hP.isLB hs]
    exact (isAdditive_iff hP.isLB).1 haddA Y a a' t
  have hmy : IsMonHom y := GlobalTheory.AbDual.isMonHom_of_classifying S B A A'' (swap P) Q k1 k2.additive hs haddSS y hy
  have mx : Mono x := mono_of_isPerfect h1 hP x hx
  have my : Mono y := mono_of_isPerfect k1 hP.swap y hy
  have ix : IsIso x := by
    rcases le_or_gt g g' with hle | hlt
    · exact GlobalTheory.AbMonoIso.isIso_of_mono S B B' hB hB' g' g hg' (hd' g hg) hle x hmx mx
    · by_cases hS : Nonempty S
      · exfalso
        have iy := GlobalTheory.AbMonoIso.isIso_of_mono S A A'' hA hA'' g g' hg (hdQ g' hg') hlt.le y hmy my
        exact absurd (GlobalTheory.relDim_unique_of_iso_grp S hS A A'' y iy g g' hg (hdQ g' hg')) hlt.ne'
      · exact isIso_of_isEmpty (not_nonempty_iff.1 hS) x
  exact GlobalTheory.AbDual.transport S A B B' P P' h1 hP.isLB x ix hmx hx

theorem isDual_of_isPerfect (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) : IsDual A B P :=
  isDual_of_isPerfect_of_additive hD A B hA hB hg hg' hP
    (CubeNoeth.isAdditive_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)
    (CubeNoeth.isAdditive_swap_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)

end GlobalTheory.PerfectDual
