import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundleStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 400000 in

theorem GlobalTheory.Mum.exists_lift_of_lam_lift_sq : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left), IsAbelianScheme Y₀ → IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → IsSquare i l → ∀ (L₀ : LB Y₀.left) (Q : LB (Y ⊗ Y).left), L₀.IsLB → Q.IsLB → GlobalTheory.AbDual.IsAdditive Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → LBIso (Q.pull l) (abelian₂ Y₀ L₀) → ∃ L : LB Y.left, L.IsLB ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hI Y₀ _ Y _ i l hY₀ hY hgp hsq L₀ Q hL₀ hQ _ _ hΛ
  haveI : IsCommMonObj Y₀ := hY₀.comm
  obtain ⟨L, hL, hiso⟩ := GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle R R₀ π hπ (by rw [hI]; rfl) Y Y₀ i l hY hgp hsq Q L₀
    hQ hL₀ (LBIso.symm hΛ)
  exact ⟨L, hL, LBIso.symm hiso⟩
