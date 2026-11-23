import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)

namespace GlobalTheory.CechPic

theorem intCast_mul_eq_zero_of_isIntegral {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X]
    (hc : CharZero Γ(X, ⊤)) (W : X.Opens) {m : ℤ} (hm : m ≠ 0) {c : Γ(X, W)}
    (h : (m : Γ(X, W)) * c = 0) : c = 0 := by
  by_cases hW : Nonempty W
  · have hinj := AlgebraicGeometry.map_injective_of_isIntegral X (homOfLE (le_top : W ≤ ⊤))
    have hm' : (m : Γ(X, W)) ≠ 0 := by
      intro h0
      apply hm
      have : (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (m : Γ(X, ⊤)) =
          (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom 0 := by
        rw [map_intCast, map_zero, h0]
      exact_mod_cast hinj this
    exact (mul_eq_zero.1 h).resolve_left hm'
  · have hb : W = ⊥ := eq_bot_iff.2 fun x hx => (hW ⟨⟨x, hx⟩⟩).elim
    subst hb
    have := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

theorem cechLB_X_noZSMulDivisors : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) →
    ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 →
    ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  intro X _ hc f M κ _ D n m hm x hx
  have key : ∀ (V : X.Opens) (y : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V), m • y = 0 → y = 0 := by
    intro V y hy
    refine GlobalTheory.AbLaw.SecOnR.ext (R := ℤ) (f := f) fun i => ?_
    let c : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V →+ Γ(X, V ⊓ M.U i) :=
      { toFun := fun z => GlobalTheory.AbLaw.SecOnR.coord z i
        map_zero' := GlobalTheory.AbLaw.SecOnR.coord_zero i
        map_add' := fun z w => GlobalTheory.AbLaw.SecOnR.coord_add z w i }
    have hi : c (m • y) = c 0 := congrArg c hy
    rw [map_zsmul, map_zero, zsmul_eq_mul] at hi
    exact intCast_mul_eq_zero_of_isIntegral hc _ hm hi
  funext s
  refine key _ (x s) ?_
  exact congrFun hx s

end GlobalTheory.CechPic
