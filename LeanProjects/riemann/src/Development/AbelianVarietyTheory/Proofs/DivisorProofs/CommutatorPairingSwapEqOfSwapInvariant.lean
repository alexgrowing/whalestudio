import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SwapPairing

theorem weilIs_swap_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  intro S A _ _ P hA hP hiso n T u v c c' h h'
  let ψ : G2 A ⟶ G2 A := lift (snd A A) (fst A A)
  haveI : IsMonHom ψ := inferInstanceAs (IsMonHom (lift (snd A A) (fst A A)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hx : lift u 1 ≫ ψ = lift 1 u := by ext <;> simp [ψ]
  have hy : lift 1 v ≫ ψ = lift v 1 := by ext <;> simp [ψ]
  have hw : LBIso (lbPow P 1) (P.pull ψ.left) :=
    LBIso.trans (isLB_lbPow hP 1) hP (pull_isLB hP _) (lbIso_lbPow_one hP) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift u 1) (y := lift 1 v)
    globalFns_holds hAA hP hP ψ hw (by rw [hx, hy]; exact h)
  rw [Nat.cast_one, _root_.mul_one] at h1
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hP h1 h'

end GlobalTheory.SwapPairing
