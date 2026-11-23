import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

open GlobalTheory.Cartier GlobalTheory.CxPts

noncomputable section

namespace GlobalTheory.CurveSelf

theorem isSelfInter_fnB_curve : ∀ (k : Type) [CommRing k] (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'],
    IsArithVar (spMap (algebraMap k k')) 0 → ∀ (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ)
    (hc : ∀ σ y, CxPts.CInfAt (c σ) y) (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))) (a : ℝ),
    (fnB c hc hcc).IsSelfInter a → a = 1 / 2 * ∑ᶠ σ, ∑ᶠ y, c σ y := by
  intro k _ k' _ _ _ hX c hc hcc a ⟨h, hh, ha⟩
  subst ha
  have := hX.isLocallyNoetherian
  have hr : IsRatSec ((fnB c hc hcc).restr (𝟙 (Sp k'))).B (fun _ => 1) := fun a b h => by
    have hL := LB.isLB_pull (LB.isLB_triv (Sp k')) (𝟙 (Sp k'))
    obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
    have := congrArg (fun u : Γ(Sp k', _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
    simp only [Units.val_one] at this
    erw [map_one] at this
    rw [Units.val_one, mul_one]
    exact (this.symm.trans (fnOf_resG _ h.1 _))
  have e := hh.point (Sp k') (𝟙 _) hX.charZero (by rw [hX.dim_eq]; rfl) _ hr
  rw [HermLB.curveDeg] at e
  have h₁ (z : Sp k') : (((fnB c hc hcc).restr (𝟙 (Sp k'))).div hr).mult z = 0 :=
    have ⟨i, hi⟩ := exists_chart ((fnB c hc hcc).restr (𝟙 (Sp k'))).isLB z
    ((presents_divOfRatSec _ hr).isEqn i z hi).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ : k →+* ℂ) (y : CxPts (𝟙 (Sp k') ≫ spMap (algebraMap k k')) σ) :
      logNorm (((fnB c hc hcc).restr (𝟙 (Sp k'))).φ σ) (fun _ => 1) y =
        -(1 / 2) * c σ (PtsOver.map (𝟙 (Sp k')) rfl _ y) := by
    have e' := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e'
    rw [logNorm, Units.val_one, e', norm_one, Real.log_one]
    erw [Weight.pull_φ]
    change 0 - c σ _ / 2 = _
    ring
  let E (σ : k →+* ℂ) : CxPts (𝟙 (Sp k') ≫ spMap (algebraMap k k')) σ ≃ CxPts (spMap (algebraMap k k')) σ :=
    { toFun := PtsOver.map (𝟙 (Sp k')) rfl _
      invFun := PtsOver.map (𝟙 (Sp k')) (Category.id_comp _) _
      left_inv := fun y => Subtype.ext ((congrArg (· ≫ 𝟙 (Sp k')) (Category.comp_id y.1)).trans (Category.comp_id y.1))
      right_inv := fun y => Subtype.ext ((congrArg (· ≫ 𝟙 (Sp k')) (Category.comp_id y.1)).trans (Category.comp_id y.1)) }
  have h₃ (σ : k →+* ℂ) : ∑ᶠ y : CxPts (𝟙 (Sp k') ≫ spMap (algebraMap k k')) σ,
      logNorm (((fnB c hc hcc).restr (𝟙 (Sp k'))).φ σ) (fun _ => 1) y =
        -(1 / 2) * ∑ᶠ y, c σ y := by
    simp only [h₂]
    rw [← mul_finsum]
    exact congrArg _ (finsum_comp_equiv (E σ))
  simp only [h₁, h₃, Int.cast_zero, zero_mul, finsum_zero] at e
  rw [← mul_finsum] at e
  exact e.trans (by ring)

end GlobalTheory.CurveSelf
