import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

def HasGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

section

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem HasGen.mul (h : HasGen L φ ε) (h' : HasGen L φ' ε') :
    HasGen L (Sum.elim φ φ') (Sum.elim ε ε') := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, DVR.mulGen_isGen L _ _ _ _ t t' ht ht'⟩

theorem HasGen.inv (h : HasGen L φ ε) : HasGen L φ (fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, DVR.invGen_isGen L _ _ t ht⟩

theorem HasGen.pull (h : HasGen L φ ε) (f : Z ⟶ Y) : HasGen L (fun k => f ≫ φ k) ε := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, DVR.pullGen_isGen L _ _ t ht f⟩

theorem HasGen.of_formEq (hL : L.IsLB) (h : HasGen L φ ε) (e : FormEq φ ε φ' ε') : HasGen L φ' ε' := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL e t ht
  exact ⟨t', ht'⟩

end

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1])
    (hsym : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left] ![1, -1]) (n : ℕ) :
    HasGen L (K := Fin 2) ![x.left, (x ^ n).left] ![(n : ℤ) ^ 2, -1] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact hone.inv.of_formEq hL (fun U _ h => by simp [Fin.prod_univ_succ])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type])
  | more n ih₀ ih₁ =>
    refine ((hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left).mul
      ((ih₁.mul ih₁).mul (ih₀.inv.mul ((hone.mul hone).mul hsym)))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_cub (x ^ (n + 1)) x x⁻¹ h) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    push_cast
    module

theorem mulPull_of_cube_of_symm :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) ∧ MulPullSt := by
  intro hc hs
  have main : ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen := by
    intro S P n
    have hcube : HasGen P.L (thφ P.A (x3 P.A)) thε := hc S P P.L P.isLB
    have hrig : HasGen P.L (K := PUnit) (fun _ => eSec P.A) (fun _ => 1) := P.rigid
    have hneg : HasGen P.L (K := Fin 2) ![(snd P.A P.A).left,
      (snd P.A P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left] ![1, -1] := hs S P 1 P.A
    refine hasGen_pow P.isLB hcube (𝟙 P.A) ?_ ?_ n
    · refine (hrig.pull (toUnit P.A).left).of_formEq P.isLB (fun U _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine (hneg.pull (lift (𝟙 P.A) (𝟙 P.A)).left).of_formEq P.isLB (fun U _ h => ?_)
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        ← Over.comp_left, lift_snd, lift_snd_assoc]
      rfl
  exact ⟨main, fun S _ P n => main S P n⟩

end GlobalTheory.MulPull
