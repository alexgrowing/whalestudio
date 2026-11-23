import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamD

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

theorem lam_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L)) :
    pull (sqToBase (G4 (A ⊗ B)) s) (zc hD.isLB l mu α) =
      lam (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) (fst _ _) (snd _ _) := by
  haveI : IsCommMonObj A := hA.comm
  have hw : sqToBase (G4 (A ⊗ B)) s = Over.Hom.left (lift
      (toBase (G4 (A ⊗ B)) s (fst ((Over.pullback s).obj (G4 (A ⊗ B))) ((Over.pullback s).obj (G4 (A ⊗ B)))))
      (toBase (G4 (A ⊗ B)) s (snd ((Over.pullback s).obj (G4 (A ⊗ B))) ((Over.pullback s).obj (G4 (A ⊗ B)))))) := rfl
  rw [zc, hw, pull_zcPair, lift_fst, lift_snd]
  have hc : cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL) =
      cls (L.LinComb (phiL mu s) fun _ => 1) (LB.isLB_linComb hL _ _) +
        cls (P.LinComb (phiP s) fun ij => α ij.1 ij.2) (LB.isLB_linComb hD.isLB _ _) :=
    cls_tens (LB.isLB_linComb hL _ _) (LB.isLB_linComb hD.isLB _ _) (isLB_zb mu α s hD.isLB hL)
  rw [hc, cls_linComb hL, cls_linComb hD.isLB]
  rw [lam_eq_lamHom, map_add, map_sum, map_sum]
  simp only [map_zsmul, one_smul, ← lam_eq_lamHom, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, line_bundle_pairing_zeroth hD l mu s L hL e, line_bundle_pairing_first hD hD' l mu s L hL e,
    line_bundle_pairing_second hD l mu s L hL e, line_bundle_pairing_third hD hD' l mu s L hL e, lam_phiP hD hD' s, zcPair, smul_add]
  abel

end PositivityTheory.PrwZar
