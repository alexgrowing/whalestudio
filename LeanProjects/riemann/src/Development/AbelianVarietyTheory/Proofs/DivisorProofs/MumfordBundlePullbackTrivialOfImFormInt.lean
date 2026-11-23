import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame

theorem dot_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (a b : Fin g → ℂ) :
    a ⬝ᵥ Hm *ᵥ star b = star (b ⬝ᵥ Hm *ᵥ star a) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

theorem exp_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (w l : Fin g → ℂ) (n : ℤ)
    (hn : (w ⬝ᵥ Hm *ᵥ star l).im = n) :
    Complex.exp (Real.pi * (l ⬝ᵥ Hm *ᵥ star w)) = Complex.exp (Real.pi * (w ⬝ᵥ Hm *ᵥ star l)) := by
  rw [dot_herm_swap hH l w]
  set a := w ⬝ᵥ Hm *ᵥ star l
  have e : (star a : ℂ) = a + (-n : ℤ) * (2 * Complex.I) := by
    apply Complex.ext <;> simp [hn, Complex.conj_re, Complex.conj_im] <;> ring
  rw [e, mul_add, Complex.exp_add]
  have : (Real.pi : ℂ) * ((-n : ℤ) * (2 * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

end GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame GlobalTheory.TorusRM.KerTriv in

theorem GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  intro A _ _ g hA M u Hm χ hM hF w hw
  have hp : IsProjOver A.hom :=
    (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1 (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : ((abelian₂ A M).pull (pairRight (u.ex w)).left).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨t, ht⟩ := GlobalTheory.HolUnifSec.hasGen_of_periodic A hA hp _ hL' g (transUnif u w)
    (fun z => Complex.exp (Real.pi * (z ⬝ᵥ Hm *ᵥ star w))) (by
      have hd : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ Hm *ᵥ star w) := by
        simp only [dotProduct]; fun_prop
      exact ((differentiable_const _).mul hd).cexp) (fun z => Complex.exp_ne_zero _) (by
      intro l hl i z hz
      obtain ⟨n, hn⟩ := hw l hl
      rw [transUnif_factor u hF w ⟨l, hl⟩ i z hz, add_dotProduct, mul_add, Complex.exp_add,
        exp_swap hF.1 w l n hn]
      ring)
  have hρ : fst A (𝟙_ (Over (Sp ℂ))) ≫ pairRight (u.ex w) =
      lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) := by
    simp only [pairRight, comp_lift, Category.comp_id]
    rw [← Category.assoc, toUnit_unique (fst A (𝟙_ (Over (Sp ℂ))) ≫ toUnit A) (snd A (𝟙_ (Over (Sp ℂ))))]
  have key : (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫ (pairRight (u.ex w)).left) =
      (fun _ : PUnit => (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : ∃ t : (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫
      (pairRight (u.ex w)).left) (fun _ => 1)).Gen, t.IsGen :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (fst A (𝟙_ (Over (Sp ℂ)))).left⟩
  rw [key] at H
  exact H
