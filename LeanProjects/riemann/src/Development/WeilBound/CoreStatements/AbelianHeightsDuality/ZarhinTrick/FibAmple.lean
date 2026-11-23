import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FourfoldProductExt
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FinSurjOfQuasiInverse
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleB
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfTwoSmul
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.TwoClsEMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfLbPow
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogeny
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

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

private theorem eMap_comp_eMap'_eq_id_pow [IsCommMonObj A] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (m : ℕ) : eMap mu α m ≫ eMap' mu α m = 𝟙 (G4 (A ⊗ B)) ^ (2 * m) := by
  apply fourfold_product_ext
  intro i
  rw [Category.assoc, eMap', g4lift_prj]
  ext1
  · rw [Category.assoc, lift_fst, Category.assoc, pow_comp', Category.id_comp, MonObj.comp_mul, comp_pow',
      comp_prod_zpow]
    simp only [← Category.assoc, eMap, g4lift_prj, lift_fst, lift_snd]
    simp only [pow_comp']
    have key : ∀ j : Fin 4, (((prj (A ⊗ B) j ≫ snd A B) ≫ mu) ^ (2 * m)) ^ α i j =
        (((prj (A ⊗ B) j ≫ snd A B) ≫ mu) ^ α i j) ^ (2 * m) := by
      intro j
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    simp only [key, Finset.prod_pow, mul_pow, inv_pow, inv_mul_cancel_right]
  · rw [Category.assoc, lift_snd, Category.assoc, pow_comp', Category.id_comp, ← Category.assoc, eMap,
      g4lift_prj, lift_snd]

theorem relAmple_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) (g : ℕ) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom)
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    Out.RelAmple ((Over.pullback s).obj (G4 (A ⊗ B))) (zb mu α s P L) := by
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj B := hB.comm
  have hP : P.IsLB := hD.isLB
  have hAB : IsAbelianScheme (A ⊗ B) := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4 : IsAbelianScheme (G4 (A ⊗ B)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  have hG : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ B))) := Z2.isAbelianScheme_pb s _ h4
  have hfin := isFinite_mu_fibre hA hB g hgA hgB l mu m hm h₁ h₂ s L hL ha
  have hlp := relAmple_lPart hA hB mu s L hL ha hfin
  have hlpLB : (lPart mu s L).IsLB := LB.isLB_linComb hL _ _
  have hzb : (zb mu α s P L).IsLB := isLB_zb mu α s hP hL
  have c1 : (Over.pullback s).map (eMap' mu α m) ≫ (Over.pullback s).map (eMap mu α m) =
      𝟙 _ ^ (2 * m) := by
    rw [← Functor.map_comp, eMap'_comp_eMap, Z2.pb_map_id_pow]
  have c2 : (Over.pullback s).map (eMap mu α m) ≫ (Over.pullback s).map (eMap' mu α m) =
      𝟙 _ ^ (2 * m) := by
    rw [← Functor.map_comp, eMap_comp_eMap'_eq_id_pow, Z2.pb_map_id_pow]
  have hE1 : ((zb mu α s P L).pull (Over.Hom.left ((Over.pullback s).map (eMap mu α m)))).IsLB :=
    LB.isLB_pull hzb _
  have hE := two_cls_eMap hA hB hD hD' l mu α s L hL e m hm h₁ h₂ hα hα' hE1 hlpLB
  have hEa := relAmple_of_two_smul hG hE1 hlpLB 2 (by norm_num) hE hlp
  obtain ⟨hE'fin, -, -, -⟩ := Z2.fin_surj_core hG hG ((Over.pullback s).map (eMap' mu α m))
    ((Over.pullback s).map (eMap mu α m)) (2 * m) (by omega) c1 c2 hlpLB hlp
  haveI := hE'fin
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ B))).hom := hG.proper
  have h2 := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom ((Over.pullback s).map (eMap' mu α m)) hE1 hEa
  have hNLB := LB.isLB_pull hE1 (Over.Hom.left ((Over.pullback s).map (eMap' mu α m)))
  have hP2 : ((zb mu α s P L).pull (Over.Hom.left (𝟙 ((Over.pullback s).obj (G4 (A ⊗ B))) ^ (2 * m)))).IsLB :=
    LB.isLB_pull hzb _
  have hpow := Z2.two_cls_pow hA hB hD hD' l mu α s L hL e (2 * m) hP2
  have hN : cls _ hNLB = cls _ hP2 := by
    rw [cls_pull hE1, cls_pull hzb, cls_pull hzb, ← pull_comp, ← Over.comp_left, c1]
  have hM : (lbPow (zb mu α s P L) ((2 * m) ^ 2)).IsLB := GlobalTheory.isLB_lbPow hzb _
  have key : 2 • cls _ hM = 2 • cls _ hNLB := by
    rw [hN, hpow, cls_lbPow hzb, smul_smul]
  have h3 := relAmple_of_two_smul hG hM hNLB 2 (by norm_num) key h2
  exact relAmple_of_lbPow hG hzb ((2 * m) ^ 2) (Nat.one_le_pow _ _ (by omega)) h3

end PositivityTheory.PrwZar
