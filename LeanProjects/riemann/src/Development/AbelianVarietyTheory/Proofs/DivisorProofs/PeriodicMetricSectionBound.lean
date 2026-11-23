import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTorusFlatCoordsInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainOfIsLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralFderivApplyEqZeroOfPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSetIntegralFundamentalDomainEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTwoImQuadNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D10OfRealEqMulLog

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ScalarAcyc

theorem fundDomain {g : ℕ} (M : Submodule ℤ (Fl g)) (hM : IsLat M) :
    ∃ D : Set (Fl g), MeasurableSet D ∧ Bornology.IsBounded D ∧
      IsAddFundamentalDomain M.toAddSubgroup D volume :=
  GlobalTheory.TorsionForm.FlatAcyc.exists_fundamentalDomain_of_isLat M hM

theorem integral_fderiv_eq_zero {g : ℕ} (M : Submodule ℤ (Fl g)) (D : Set (Fl g))
    (hDm : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (hD : IsAddFundamentalDomain M.toAddSubgroup D volume) (F : Fl g → ℂ) (hF : ContDiff ℝ 1 F)
    (hper : ∀ l ∈ M, ∀ x, F (x + l) = F x) (y : Fl g) : ∫ x in D, fderiv ℝ F x y = 0 :=
  GlobalTheory.TorsionForm.FlatAcyc.setIntegral_fderiv_apply_eq_zero_of_periodic M D hDm hDb hD F hF hper y

theorem eq_zero_of_integral {g : ℕ} (M : Submodule ℤ (Fl g)) (hM : IsLat M) (D : Set (Fl g))
    (hDm : MeasurableSet D) (hD : IsAddFundamentalDomain M.toAddSubgroup D volume)
    (q : Fl g → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x) (hper : ∀ l ∈ M, ∀ x, q (x + l) = q x)
    (hint : IntegrableOn q D) (h0 : ∫ x in D, q x = 0) (x : Fl g) : q x = 0 :=
  GlobalTheory.TorsionForm.FlatAcyc.eq_zero_of_setIntegral_fundamentalDomain_eq_zero M D hM hDm hD q hq hq0 hper hint h0 x

theorem quad_nonneg {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T) (x : Fin g → ℂ) :
    (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).im = 0 ∧
    0 ≤ (∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c * (starRingEnd ℂ (x a) * x c)).re :=
  GlobalTheory.siegel_two_im_quad_nonneg T hT x

theorem div_identity {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (H : (Fin g → ℂ) → ℝ)
    (hH : ContDiff ℝ ∞ H) (hHpos : ∀ z, 0 < H z) (u : (Fin g → ℂ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (z : Fin g → ℂ) :
    ∑ a, d10 (fun z' => (H z' : ℂ) * starRingEnd ℂ (u z') * ∑ c, G a c * d01 u z' (ev c)) z (ev a) =
      (H z : ℂ) * starRingEnd ℂ (u z) * (∑ a, ∑ c, G a c *
        (d10 (fun z' => d01 u z' (ev c)) z (ev a) +
          d10 (fun z' => (Real.log (H z') : ℂ)) z (ev a) * d01 u z (ev c))) +
      (H z : ℂ) * ∑ a, ∑ c, G a c * (starRingEnd ℂ (d01 u z (ev a)) * d01 u z (ev c)) :=
  GlobalTheory.TorsionForm.FlatAcyc.DivId.divergence_identity G H hH hHpos u hu z

theorem torus_vanish {g : ℕ} {ι : Type} [Fintype ι] (M : Submodule ℤ (Fl g)) (hM : IsLat M)
    (F : ι → Fl g → ℂ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hper : ∀ i, ∀ l ∈ M, ∀ x, F i (x + l) = F i x) (y : ι → Fl g) (q : Fl g → ℝ)
    (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (hqF : ∀ x, (q x : ℂ) = ∑ i, fderiv ℝ (F i) x (y i)) (x : Fl g) : q x = 0 := by
  obtain ⟨D, hDm, hDb, hD⟩ := fundDomain M hM
  have hcomp : IsCompact (closure D) := hDb.isCompact_closure
  have hint : ∀ i, IntegrableOn (fun x => fderiv ℝ (F i) x (y i)) D := fun i =>
    (((((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn).integrableOn_compact
      hcomp).mono_set subset_closure
  have hqper : ∀ l ∈ M, ∀ x, q (x + l) = q x := by
    intro l hl x
    have hfd : ∀ i, fderiv ℝ (F i) (x + l) = fderiv ℝ (F i) x := by
      intro i
      have : (fun x' => F i (x' + l)) = F i := funext fun x' => hper i l hl x'
      rw [← fderiv_comp_add_right, this]
    have h1 := hqF (x + l)
    have h2 := hqF x
    simp only [hfd] at h1
    exact_mod_cast h1.trans h2.symm
  have hqi : IntegrableOn q D := (hq.continuousOn.integrableOn_compact hcomp).mono_set subset_closure
  have h0 : ∫ x in D, q x = 0 := by
    have : ((∫ x in D, q x : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      simp_rw [hqF]
      rw [integral_finset_sum _ fun i _ => hint i]
      exact Finset.sum_eq_zero fun i _ =>
        integral_fderiv_eq_zero M D hDm hDb hD (F i) (hF i) (hper i) (y i)
    exact_mod_cast this
  exact eq_zero_of_integral M hM D hDm hD q hq hq0 hqper hqi h0 x

def perLin {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) : Fl g →ₗ[ℝ] (Fin g → ℂ) where
  toFun := per T
  map_add' x y := by
    have e : (fun i => ((x + y) (Sum.inl i) : ℂ)) =
        (fun i => (x (Sum.inl i) : ℂ)) + fun i => (y (Sum.inl i) : ℂ) := by ext; simp
    simp only [per, e, Matrix.add_vecMul]
    ext i; simp; try ring
  map_smul' r x := by
    have e : (fun i => ((r • x) (Sum.inl i) : ℂ)) = (r : ℂ) • fun i => (x (Sum.inl i) : ℂ) := by
      ext; simp
    simp only [per, e, Matrix.smul_vecMul]
    ext i; simp [Complex.real_smul]; try ring

end GlobalTheory.ScalarAcyc

namespace GlobalTheory.ScalarAcyc

theorem vanish : ∀ {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T)
    (M : Submodule ℤ (Fl g)) (hM : IsLat M) (H : (Fin g → ℂ) → ℝ) (hH : ContDiff ℝ ∞ H)
    (hHpos : ∀ z, 0 < H z) (u : (Fin g → ℂ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (J : Fl g → (Fin g → ℂ) → ℂ) (hu_per : ∀ l ∈ M, ∀ z, u (z + per T l) = J l z * u z)
    (hdu_per : ∀ l ∈ M, ∀ z c, d01 u (z + per T l) (ev c) = J l z * d01 u z (ev c))
    (hH_per : ∀ l ∈ M, ∀ z, H (z + per T l) * ‖J l z‖ ^ 2 = H z) (k : ℝ) (hk : 0 < k)
    (heq : ∀ z, ∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c *
      (d10 (fun z' => d01 u z' (ev c)) z (ev a) +
        d10 (fun z' => (Real.log (H z') : ℂ)) z (ev a) * d01 u z (ev c)) = k * u z),
    ∀ z, u z = 0 := by
  intro g T hT M hM H hH hHpos u hu J hu_per hdu_per hH_per k hk heq
  set G : Matrix (Fin g) (Fin g) ℂ := (2 : ℂ) • T.map fun t => (t.im : ℂ) with hG
  set Fa : Fin g → (Fin g → ℂ) → ℂ :=
    fun a z => (H z : ℂ) * starRingEnd ℂ (u z) * ∑ c, G a c * d01 u z (ev c) with hFa_def
  set Q : (Fin g → ℂ) → ℂ :=
    fun z => ∑ a, ∑ c, G a c * (starRingEnd ℂ (d01 u z (ev a)) * d01 u z (ev c)) with hQ_def
  set q : (Fin g → ℂ) → ℝ := fun z => H z * k * ‖u z‖ ^ 2 + H z * (Q z).re with hq_def

  have hfu : ContDiff ℝ ∞ (fderiv ℝ u) := (contDiff_infty_iff_fderiv.1 hu).2
  have hap : ∀ v, ContDiff ℝ ∞ (fun z => fderiv ℝ u z v) := fun v => hfu.clm_apply contDiff_const
  have hd01 : ∀ c, ContDiff ℝ ∞ (fun z => d01 u z (ev c)) := by
    intro c
    show ContDiff ℝ ∞ (fun z => (1 / 2 : ℂ) • (fderiv ℝ u z (ev c) +
      Complex.I • fderiv ℝ u z (Complex.I • ev c)))
    exact ((hap _).add ((hap _).const_smul Complex.I)).const_smul _
  have hHc : ContDiff ℝ ∞ (fun z => (H z : ℂ)) := Complex.ofRealCLM.contDiff.comp hH
  have hconj : ContDiff ℝ ∞ (fun z => starRingEnd ℂ (u z)) := Complex.conjCLE.contDiff.comp hu
  have hFa : ∀ a, ContDiff ℝ ∞ (Fa a) := fun a =>
    (hHc.mul hconj).mul (ContDiff.sum fun c _ => contDiff_const.mul (hd01 c))

  have hFa_per : ∀ a, ∀ l ∈ M, ∀ z, Fa a (z + per T l) = Fa a z := by
    intro a l hl z
    show (H (z + per T l) : ℂ) * starRingEnd ℂ (u (z + per T l)) *
      ∑ c, G a c * d01 u (z + per T l) (ev c) = (H z : ℂ) * starRingEnd ℂ (u z) * ∑ c, G a c * d01 u z (ev c)
    rw [hu_per l hl z]
    simp only [hdu_per l hl z]
    have hS : ∑ c, G a c * (J l z * d01 u z (ev c)) = J l z * ∑ c, G a c * d01 u z (ev c) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    rw [hS, map_mul, ← hH_per l hl z]
    have hJ := Complex.conj_mul' (J l z)
    push_cast
    linear_combination ((H (z + per T l) : ℂ) * starRingEnd ℂ (u z) *
      ∑ c, G a c * d01 u z (ev c)) * hJ

  have hdiv : ∀ z, (q z : ℂ) = ∑ a, d10 (Fa a) z (ev a) := by
    intro z
    have h2 := div_identity G H hH hHpos u hu z
    have h3 := quad_nonneg T hT (fun a => d01 u z (ev a))
    rw [← hG] at h3
    have hQz : Q z = ((Q z).re : ℂ) := Complex.ext (by simp) (by simpa [hQ_def] using h3.1)
    have hu2 := Complex.conj_mul' (u z)
    rw [show (∑ a, d10 (Fa a) z (ev a)) = _ from h2, heq z]
    rw [show (∑ a, ∑ c, G a c * (starRingEnd ℂ (d01 u z (ev a)) * d01 u z (ev c))) = Q z from rfl,
      hQz]
    simp only [hq_def]
    push_cast
    linear_combination -((H z : ℂ) * k) * hu2
  have hq0 : ∀ z, 0 ≤ q z := by
    intro z
    have h3 := quad_nonneg T hT (fun a => d01 u z (ev a))
    rw [← hG] at h3
    have := hHpos z
    simp only [hq_def]
    have hQ : 0 ≤ (Q z).re := h3.2
    positivity
  have hqc : Continuous q := by
    have hQc : Continuous Q := continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ =>
      continuous_const.mul ((Complex.continuous_conj.comp (hd01 a).continuous).mul (hd01 c).continuous)
    exact ((hH.continuous.mul continuous_const).mul (hu.continuous.norm.pow 2)).add
      (hH.continuous.mul (Complex.continuous_re.comp hQc))

  set φ : Fl g →L[ℝ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (perLin T) with hφ
  have hφx : ∀ x, φ x = per T x := fun x => rfl
  have hinv := flatOf_per_inv T hT.2
  have hcomp : ∀ a (c : ℂ) x y, fderiv ℝ (fun x => c * Fa a (φ x)) x y =
      c * fderiv ℝ (Fa a) (φ x) (φ y) := by
    intro a c x y
    have hd : DifferentiableAt ℝ (Fa a) (φ x) := ((hFa a).differentiable (by simp)) _
    have h1 := (hd.hasFDerivAt.comp x φ.hasFDerivAt).const_mul c
    rw [show (fun x => c * Fa a (φ x)) = fun y => c * (Fa a ∘ φ) y from rfl, h1.fderiv]
    simp
  let F : Fin g ⊕ Fin g → Fl g → ℂ := Sum.elim (fun a x => (1 / 2 : ℂ) * Fa a (φ x))
    (fun a x => -(Complex.I / 2) * Fa a (φ x))
  let y : Fin g ⊕ Fin g → Fl g :=
    Sum.elim (fun a => flatOf T (ev a)) (fun a => flatOf T (Complex.I • ev a))
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    rintro (a | a)
    · exact contDiff_const.mul (((hFa a).comp φ.contDiff).of_le (by simp))
    · exact contDiff_const.mul (((hFa a).comp φ.contDiff).of_le (by simp))
  have hFper : ∀ i, ∀ l ∈ M, ∀ x, F i (x + l) = F i x := by
    rintro (a | a) l hl x
    · show (1 / 2 : ℂ) * Fa a (φ (x + l)) = (1 / 2 : ℂ) * Fa a (φ x)
      rw [map_add, hφx l, hFa_per a l hl]
    · show -(Complex.I / 2) * Fa a (φ (x + l)) = -(Complex.I / 2) * Fa a (φ x)
      rw [map_add, hφx l, hFa_per a l hl]
  have hqF : ∀ x, ((q (φ x)) : ℂ) = ∑ i, fderiv ℝ (F i) x (y i) := by
    intro x
    rw [hdiv, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F, y, Sum.elim_inl, Sum.elim_inr]
    rw [hcomp, hcomp]
    simp only [hφx, hinv.2, d10, smul_eq_mul]
    ring
  intro z
  have h0 := torus_vanish M hM F hF hFper y (fun x => q (φ x)) (hqc.comp φ.continuous)
    (fun x => hq0 _) hqF (flatOf T z)
  simp only [hφx, hinv.2] at h0
  have h3 := quad_nonneg T hT (fun a => d01 u z (ev a))
  rw [← hG] at h3
  have hQ : 0 ≤ (Q z).re := h3.2
  have hH0 := hHpos z
  have hA : H z * k * ‖u z‖ ^ 2 = 0 := by
    have : 0 ≤ H z * k * ‖u z‖ ^ 2 := by positivity
    have : 0 ≤ H z * (Q z).re := by positivity
    simp only [hq_def] at h0
    linarith
  have : ‖u z‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 hA with h | h
    · exact absurd h (by positivity)
    · exact h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

end GlobalTheory.ScalarAcyc
