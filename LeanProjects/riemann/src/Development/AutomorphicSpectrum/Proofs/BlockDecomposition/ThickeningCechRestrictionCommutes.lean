import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem pullLE_oneOn_eq_congr {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y}
    (v : LB.Iso N (N'.pull β)) (hL : (pw N 0).IsLB) (hM : ((pw N' 0).pull β).IsLB)
    (hw : (pullPow v 0).IsGen) (V : Y.Opens) (V' : X.Opens) (e : V' ≤ β ⁻¹ᵁ V) :
    SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V) =
      SecOn.congr hL hM (pullPow v 0) hw V' (oneOn N rfl V') := by
  refine GlobalTheory.LB.sec_ext_of_cover hL.cover fun p q => ?_
  have h := SecOn.coord_congr hL hM (pullPow v 0) hw (oneOn N rfl V') p q
    (O := V' ⊓ ((pw N' 0).pull β).U p ⊓ (pw N 0).U q) inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right)
  have c1 : GlobalTheory.LB.coord (SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V)) p = 1 := by
    rw [SecOn.coord_pullLE]
    exact map_one _
  have c2 : GlobalTheory.LB.coord (oneOn N (rfl : (0 : ℤ) = 0) V') q = 1 := rfl
  have c3 : (show Γ(X, ((pw N' 0).pull β).U p ⊓ (pw N 0).U q)ˣ from (pullPow v 0).s (p, q)) = 1 :=
    zpow_zero _
  rw [c2, c3] at h
  rw [c1]
  refine Eq.trans ?_ h.symm
  simp

theorem red_oneOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  intro R _ I Y β hβ N v hN ι D hDβ a h e S
  subst h
  simp only [red, redL, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, SecOnR.pull_of, SecOnR.linEquiv_of]
  exact congrArg (SecOnR.of _ _ _) (pullLE_oneOn_eq_congr (v e) _ _ _ _ _ _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
