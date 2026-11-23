import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamC

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

omit [GrpObj A] [GrpObj B] in

theorem pull_zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y Z : Over S} (w : Z ⟶ Y) (u u' : Y ⟶ G4 (A ⊗ B)) :
    pull w.left (zcPair hP lm mu α u u') = zcPair hP lm mu α (w ≫ u) (w ≫ u') := by
  simp only [zcPair, map_add, map_sum, map_nsmul, map_zsmul, pull_evc, Category.assoc]

section Pieces

variable {P : LB (A ⊗ B).left} (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l]
  (mu : B ⟶ A) [IsMonHom mu] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left)
  (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
  {T : Over (Sp Ω)} (u u' : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B)))

include e in
theorem line_bundle_pairing_zeroth (i : Fin 4) :
    lam (pull (phiL mu s (0, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ fst A B) (T := T)
  show lam (pull (pA s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pA s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pA, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_first [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (1, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm0 := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have hm : (u * u') ≫ (pA (B := B) s i)⁻¹ = u ≫ (pA s i)⁻¹ * u' ≫ (pA s i)⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv]
    show ((u * u') ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B))⁻¹ = _
    rw [hm0, mul_inv]
    rfl
  have h1 : (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (pA (B := B) s i)⁻¹ = 1 := by
    rw [GrpObj.comp_inv]
    show ((1 : T ⟶ _) ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B))⁻¹ = 1
    rw [map_one_pt, inv_one]
  show lam (pull ((pA (B := B) s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_pt ((pA s i)⁻¹) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e,
    GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pA, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include e in
theorem line_bundle_pairing_second (i : Fin 4) :
    lam (pull (phiL mu s (2, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) (T := T)
  show lam (pull (pM mu s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pM mu s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pM, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_third [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (3, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm0 := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have hm : (u * u') ≫ (pM mu s i)⁻¹ = u ≫ (pM mu s i)⁻¹ * u' ≫ (pM mu s i)⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv]
    show ((u * u') ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu))⁻¹ = _
    rw [hm0, mul_inv]
    rfl
  have h1 : (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (pM mu s i)⁻¹ = 1 := by
    rw [GrpObj.comp_inv]
    show ((1 : T ⟶ _) ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu))⁻¹ = 1
    rw [map_one_pt, inv_one]
  show lam (pull ((pM mu s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_pt ((pM mu s i)⁻¹) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e,
    GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pM, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include hD hD' in
theorem evc_lam_key {Y : Over S} (a a' : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB (a * a') (b * b') - evc hD.isLB a b - evc hD.isLB a' b' + evc hD.isLB (1 : Y ⟶ A) (1 : Y ⟶ B) =
      evc hD.isLB a b' + evc hD.isLB a' b := by
  rw [evc_mul_left hD, evc_mul_right hD hD', evc_mul_right hD hD',
    IsAdditive.evc_one hD.isLB hD.additive]
  abel

private theorem pull_pull_phiP_eq_evc (ij : Fin 4 × Fin 4) (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    pull v.left (pull (phiP s ij) (cls P hD.isLB)) =
      evc hD.isLB (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have hv := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at hv
  rw [evc, ← pull_comp, hv]
  congr 2
  simp only [phiP, ← comp_lift, Over.comp_left]
  rfl

include hD' in
theorem lam_phiP (ij : Fin 4 × Fin 4) :
    lam (pull (phiP s ij) (cls P hD.isLB)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u' ≫ prj _ ij.2 ≫ snd A B) +
        evc hD.isLB (toBase _ s u' ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u ≫ prj _ ij.2 ≫ snd A B) := by
  simp only [GlobalTheory.CechPic.lam, pull_pull_phiP_eq_evc hD, toBase_mul, toBase_one, MonObj.mul_comp, MonObj.one_comp]
  exact evc_lam_key hD hD' _ _ _ _

end Pieces

end PositivityTheory.PrwZar
