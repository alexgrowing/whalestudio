import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.CM.PairingInj

open GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_gen_cubeLB {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (x : T ⟶ A)
    (g₁ : ∃ t : LB.Gen (cubeLB A ![fst T A ≫ x, snd T A] L), t.IsGen) : x = 1 := by
  have g₂ : HasGen L _ _ := g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem eq_of_lamEq : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (X : Over S) (f g : X ⟶ P.A), LamEq P.L f (𝟙 P.A) P.L g (𝟙 P.A) → f = g := by
  intro hL S _ P X f g h
  have := P.isAb.comm
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have C := LamCalc.lamEq_calculus S X P.A P.A P.A P.A P.L P.L P.L P.isLB P.isLB P.isLB
  have h₁ : LamEq P.L (f * g⁻¹) (𝟙 P.A) P.L (g * g⁻¹) (𝟙 P.A) :=
    ((C f g⁻¹ (𝟙 _) (𝟙 _) g g⁻¹ (𝟙 _) (𝟙 _) g (𝟙 _)).2.2.1 hT hT h).1
      (C g⁻¹ g (𝟙 _) (𝟙 _) g g (𝟙 _) (𝟙 _) g (𝟙 _)).1
  rw [mul_inv_cancel] at h₁
  have h₂ := LamCalc.lbIso_of_lamEq h₁ (fst X P.A) (snd X P.A)
  rw [Category.comp_id, MonObj.comp_one] at h₂
  refine mul_inv_eq_one.1 (eq_one_of_gen_cubeLB P.isLB P.ktriv _ (exists_gen_of_lbIso
    (LamCalc.cubeLB_isLB P.isLB _) (LamCalc.cubeLB_isLB P.isLB _) h₂.symm ?_))
  exact hasGen_of_trivial P.isLB fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])

end GlobalTheory.CM.PairingInj
