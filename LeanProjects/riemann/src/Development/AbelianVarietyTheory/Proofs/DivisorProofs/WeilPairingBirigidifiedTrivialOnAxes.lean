import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilProdEqOneOfToric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AxisPairing

theorem weilIs_comp_eq_one_of_pull_isGen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left)
    (hA : IsAbelianScheme A) (hP : P.IsLB) (ψ : A ⟶ G2 A) [IsMonHom ψ]
    (hg : ∃ t : (P.pull ψ.left).Gen, t.IsGen) {n : ℤ} {T : Over S} {u v : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs (G2 A) P n (u ≫ ψ) (v ≫ ψ) c) : c = 1 := by
  have hL : (P.pull ψ.left).IsLB := LB.isLB_pull hP ψ.left
  have h0 : GlobalTheory.CechPic.cls _ hL = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 hg
  have hw : LBIso (lbPow (P.pull ψ.left) 1) (P.pull ψ.left) := by
    have hp : (lbPow (P.pull ψ.left) 1).IsLB := LB.isLB_pull hL _
    refine (GlobalTheory.CechPic.cls_eq_iff hp hL).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hL 1 hp, one_smul]
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds hA hL hP ψ hw h
  rw [Nat.cast_one, _root_.mul_one] at h1
  have h2 := GlobalTheory.SiegelOfTheta.weilIs_of_pow GlobalTheory.globalFns_holds hA hL hL 0
    (by rw [h0, zero_smul]) h1
  rw [pow_zero] at h2
  exact GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hA hL h1 h2

theorem axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  intro S A _ _ P hA hP h₂ h₁ n T u v c
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_id_one A A
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_one_id A A
  have e₁ : ∀ w : T ⟶ A, w ≫ lift (𝟙 A) (1 : A ⟶ A) = lift w 1 := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  have e₂ : ∀ w : T ⟶ A, w ≫ lift (1 : A ⟶ A) (𝟙 A) = lift 1 w := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← e₁ u, ← e₁ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₁ h
  · rw [← e₂ u, ← e₂ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₂ h

end GlobalTheory.AxisPairing
