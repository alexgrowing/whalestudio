import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPull

theorem weilIs_diag_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left),
    IsAbelianScheme A → P.IsLB → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    Out.WeilIs (G2 A) P n (lift u u) (lift v v) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n u v c' →
    c = c' := by
  intro S A _ _ P hA hP n T u v c c' h h'
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hw : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1) (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    have h1 : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 1).IsLB := LB.isLB_linComb hL _ _
    refine (CechPic.cls_eq_iff h1 hL).1 ?_
    rw [CechPic.cls_lbPow hL, one_smul]
  have hu : u ≫ lift (𝟙 A) (𝟙 A) = lift u u := by simp
  have hv : v ≫ lift (𝟙 A) (𝟙 A) = lift v v := by simp
  rw [← hu, ← hv] at h
  have h2 := WeilIsogeny.weilIs_pull_hom globalFns_holds hA hL hP (lift (𝟙 A) (𝟙 A)) hw h
  rw [Nat.cast_one, Int.mul_one] at h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hA hL h2 h'

end GlobalTheory.DiagPull
