import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianIsogenyExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGeneratorCharTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivializationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginaryStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

open GlobalTheory.CechPic GlobalTheory.RealMult.Elliptic

theorem hasGen_lam_pull_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M M' : LB A.left}
    (hM : M.IsLB) (hM' : M'.IsLB) (α : A ⟶ A)
    (h : LBIso (abelian₂ A M') ((abelian₂ A M).pull (lift (fst A A) (snd A A ≫ α)).left)) {T : Over S} (x : T ⟶ A)
    (hx : HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left)) :
    HasGen ((abelian₂ A M').pull (lift (fst A T) (snd A T ≫ x)).left) := by
  have hl : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hl' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _
  have h₁ : lam (cls M' hM') (fst A A) (snd A A) = lam (cls M hM) (fst A A) (snd A A ≫ α) :=
    (cls_cube_two hM' _ _ hl').symm.trans
      (((cls_eq_iff hl' (pull_isLB hl _)).2 h).trans (cls_pull_lam hM _ _ _))
  have h₂ : lam (cls M hM) (fst A T) (snd A T ≫ x) = 0 :=
    (cls_pull_lam hM _ _ (pull_isLB hl _)).symm.trans ((cls_eq_zero_iff (pull_isLB hl _)).2 hx)
  have h₃ := congrArg (CechPic.pull (lift (snd A T ≫ x) (fst A T)).left) h₁
  have h₄ := congrArg (CechPic.pull (lift (fst A T ≫ α) (snd A T)).left) h₂
  rw [pull_lam, pull_lam, lift_fst, lift_snd, lift_snd_assoc] at h₃
  rw [pull_lam, map_zero, lift_fst, lift_snd_assoc] at h₄
  refine (cls_eq_zero_iff (pull_isLB hl' _)).1 ?_
  rw [cls_pull_lam hM', lam_comm, h₃, lam_comm, h₄]

theorem comp_eq_one_of_lam_triv_of_pull_pos : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (f : A ⟶ A),
    M.IsLB → IsFactorAH u Hm χ →
    ∀ (M' : LB A.left) (u' : HolUnif A M' g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (α : A ⟶ A),
    M'.IsLB → u'.IsAH Hm' χ' → IsMonHom α → LBIso (abelian₂ A M') ((abelian₂ A M).pull (lift (fst A A) (snd A A ≫ α)).left) →
    (∀ w, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → u.ex w ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro g A _ hA M u Hm χ f hM hF M' u' Hm' χ' α hM' hAH _ hiso hf T x hx
  haveI := hA.comm
  obtain ⟨P, ψ, ρ, N, hN, hψ, hρ, h₁, h₂, h₃⟩ := GlobalTheory.T.polarized_abelian_isogeny_exists g A hA M' u' Hm' χ' hM' hAH
  have hk : x ^ (N * N) = 1 := GlobalTheory.T.isogeny_torsion_generator_power A hA M' hM' P ψ ρ N hψ hρ h₁ h₂ h₃ T x
    (hasGen_lam_pull_of_lbIso hM hM' α hiso x hx)
  refine GlobalTheory.T.torsion_generator_char_trivial A hA M f (N * N) hM (Nat.mul_pos hN hN) (fun y hy => ?_) T x hk hx
  obtain ⟨w, rfl⟩ := u.ex_onto y
  obtain ⟨θ, hθ, h0, hp⟩ := GlobalTheory.T.theta_multiplier_trivialization g A hA M u Hm χ hM hF w hy
  exact hf w (GlobalTheory.T.theta_multiplier_integral_imaginary g u.Λ u.full Hm hF.1 w θ hθ h0 hp)

end GlobalTheory.TorusRM
