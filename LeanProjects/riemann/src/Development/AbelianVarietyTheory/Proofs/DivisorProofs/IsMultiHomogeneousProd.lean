import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockSphereMeanLinForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsEqISup

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open GlobalTheory.IndefiniteRowSideFullHecke.FramedLatticeZeroCycleHeight

namespace GlobalTheory.ZeroCycleHt

theorem linSubst_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f g : MvPolynomial (Fin B × Fin N) R) : linSubst M (f * g) = linSubst M f * linSubst M g := by
  simp [linSubst]

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Function.Surjective w.mulVec) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  classical
  choose x hx using fun j : Fin N => hw (Pi.single j 1)
  refine ⟨Matrix.of fun k j => x j k, ?_⟩
  ext i j
  have := congrFun (hx j) i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [this, Pi.single_apply]

theorem formHeight_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ δ' : ℕ)
    {w : Matrix (Fin N) (Fin n) F} {P : Matrix (Fin n) (Fin N) F} (hP : w * P = 1)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (hg : g ≠ 0)
    (ha : IsMultiHomogeneous a f) (ha' : IsMultiHomogeneous a' g) :
    formHeight (δ + δ') w A (f * g) = formHeight δ w A f + formHeight δ' w A g := by
  have hlf := GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hlg := GlobalTheory.HeightUnique.linSubst_ne_zero hP hg
  have hfin : ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w (f * g))) =
      ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w f)) +
        ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w g)) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite _ hlf) (gauss_abs_log_support_finite _ hlg)]
    refine finsum_congr fun v => ?_
    rw [linSubst_mul, gauss_abs_mul v _ _ hlf hlg,
      Real.log_mul (gauss_abs_pos_of_ne_zero v _ hlf).ne' (gauss_abs_pos_of_ne_zero v _ hlg).ne']
  have hne : ∀ (σ : F →+* ℂ) {h : MvPolynomial (Fin B × Fin N) F}, h ≠ 0 →
      linSubst (A σ) (MvPolynomial.map σ h) ≠ 0 := fun σ h hh =>
    GlobalTheory.HeightUnique.linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h0 =>
      hh (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  have hinf : ∀ σ : F →+* ℂ, blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ (f * g))) =
      blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
        blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ g)) := by
    intro σ
    rw [map_mul, linSubst_mul]
    exact sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N a a' _ _ (hne σ hf) (hne σ hg)
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a f ha σ))
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a' g ha' σ))
  unfold formHeight
  rw [hfin]
  simp only [hinf, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
  ring

theorem formHeight_one {F : Type} [Field F] [NumberField F] {B N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) :
    formHeight 0 w A (1 : MvPolynomial (Fin B × Fin N) F) = 0 := by
  have h1 : ∀ v : FinitePlace F, gaussAbs v (1 : MvPolynomial (Fin B × Fin n) F) = 1 := fun v => by
    simpa using GlobalTheory.HeightUnique.gaussAbs_C (σ := Fin B × Fin n) v (1 : F)
  unfold formHeight
  simp [linSubst, h1, blockSphereMean]

end GlobalTheory.ZeroCycleHt
