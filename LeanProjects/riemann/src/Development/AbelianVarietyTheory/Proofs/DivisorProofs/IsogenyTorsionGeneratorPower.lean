import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIsoOfSurjectivePrincipalPairing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

section SlopeTestRemainingChoices

open GlobalTheory GlobalTheory.CM GlobalTheory.KerPow GlobalTheory.CM.PairingIso

theorem eq_one_of_lam_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) [IsCommMonObj P.A] {T : Over S}
    (z : T ⟶ P.A) (h : lam (cls P.L P.isLB) (fst T P.A ≫ z) (snd T P.A) = 0) : z = 1 := by
  have hL := P.isLB
  have hc : (cubeLB P.A ![fst T P.A ≫ z, snd T P.A] P.L).IsLB := LB.isLB_linComb hL _ _
  have g₂ : GlobalTheory.KerPow.HasGen P.L
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) :=
    (cls_eq_zero_iff hc).1 ((cls_cube_two hL _ _ hc).trans h)
  have g₃ : LocGen P.L (fst T P.A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum P.A ![fst T P.A ≫ z, snd T P.A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T P.A).left z.left (b := (fst T P.A ≫ z).left) rfl
  have b₀ := locGen_base hL (fst T P.A).left (1 : T ⟶ P.A).left (b := (1 : T ⊗ P.A ⟶ P.A).left)
    (congrArg (fun q : T ⊗ P.A ⟶ P.A => q.left) (MonObj.comp_one (fst T P.A) : fst T P.A ≫ (1 : T ⟶ P.A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ P.A ⟶ P.A).left, (fst T P.A ≫ z).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen P.ktriv z (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T P.A ≫ z) * snd T P.A).left * (k (fst T P.A ≫ z).left)⁻¹ * (k (snd T P.A).left)⁻¹ *
    k (1 : T ⊗ P.A ⟶ P.A).left *
    (k (1 : T ⊗ P.A ⟶ P.A).left ^ (1 : ℤ) * k (fst T P.A ≫ z).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T P.A ≫ z) * snd T P.A).left ^ (1 : ℤ) * k (snd T P.A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end SlopeTestRemainingChoices

end GlobalTheory.KillSquare

namespace GlobalTheory.KillSquare

open GlobalTheory.CechPic

theorem pow_sq_eq_one_of_lam_trivial : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), IsMonHom ψ → IsMonHom ρ →
      ψ ≫ ρ = (𝟙 A) ^ N → ρ ≫ ψ = (𝟙 P.A) ^ N →
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ^ (N * N) = 1 := by
  intro A _ hA M hM P ψ ρ N hψ hρ h1 h2 hiso T x hx
  haveI : IsCommMonObj A := hA.comm
  haveI := P.isAb
  have hL := P.isLB
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ P.A P.isAb P.L hL
  set ℓ := cls P.L hL
  set m := cls M hM

  have hlamA : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hpair : lam m (fst A A) (snd A A) = lam ℓ (fst A A ≫ ψ) (snd A A ≫ ψ) := by
    have hlamP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb hL _ _
    have e := (cls_eq_iff hlamA (pull_isLB hlamP _)).2 hiso
    exact (cls_cube_two hM (fst A A) (snd A A) hlamA).symm.trans (e.trans (Elliptic.cls_pull_lam hL _ _ _))

  have hx0 : lam m (fst A T) (snd A T ≫ x) = 0 := by
    rw [← Elliptic.cls_pull_lam hM _ _ (pull_isLB hlamA _)]
    exact (cls_eq_zero_iff _).2 hx
  have e1 := congrArg (pull (lift (fst A T) (snd A T ≫ x)).left) hpair
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e1
  rw [e1] at hx0

  have e2 := congrArg (pull (lift (fst P.A T ≫ ρ) (snd P.A T)).left) hx0
  simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, Category.assoc] at e2
  have e3 : fst P.A T ≫ ρ ≫ ψ = fst P.A T ^ N := by
    rw [h2, MonObj.comp_pow, Category.comp_id]
  rw [e3, lam_pow_left hL hΘ, ← lam_pow_right hL hΘ, ← MonObj.comp_pow] at e2

  have hz : (x ≫ ψ) ^ N = 1 := by
    refine GlobalTheory.KillSquare.eq_one_of_lam_eq_zero P _ ?_
    have e4 := congrArg (pull (lift (snd T P.A) (fst T P.A)).left) e2
    simp only [pull_lam, map_zero, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at e4
    rw [lam_comm] at e4
    simpa only [Category.assoc] using e4
  rw [pow_mul]
  have e5 : x ^ N = (x ≫ ψ) ≫ ρ := by
    rw [Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
  rw [e5, ← MonObj.pow_comp, hz, MonObj.one_comp]

end GlobalTheory.KillSquare
