import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FockMonoForm

open MvPolynomial

variable {σ : Type}

def fct (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

theorem fct_pos (α : σ →₀ ℕ) : 0 < fct α := Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem fct_add_single (α : σ →₀ ℕ) (v : σ) : fct (α + Finsupp.single v 1) = (α v + 1) * fct α := by
  classical
  have hs : (α + Finsupp.single v 1).support ⊆ insert v α.support := by
    intro u hu
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply] at hu
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases h : v = u
    · exact Or.inl h.symm
    · right; simpa [h] using hu
  unfold fct
  rw [Finsupp.prod_of_support_subset _ hs _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset α (Finset.subset_insert v α.support) _ (fun _ _ => Nat.factorial_zero),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v α.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v α.support)]
  have : ∀ u ∈ (insert v α.support).erase v,
      ((α + Finsupp.single v 1 : σ →₀ ℕ) u).factorial = (α u).factorial := by
    intro u hu
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Finset.ne_of_mem_erase hu).symm, add_zero]
  rw [Finset.prod_congr rfl this, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

def form0 (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ α ∈ Q.support, (fct α : ℂ) * (star (coeff α P) * coeff α Q)

theorem fischerSumSupport_eq_sum_factorial_coeff (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : Q.support ⊆ s) :
    form0 P Q = ∑ α ∈ s, (fct α : ℂ) * (star (coeff α P) * coeff α Q) := by
  unfold form0
  apply Finset.sum_subset h
  intro α _ hα
  rw [notMem_support_iff.mp hα]; simp

def form : MvPolynomial σ ℂ →ₗ⋆[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) form0
    (fun P P' Q => by
      rw [fischerSumSupport_eq_sum_factorial_coeff (P + P') Q Q.support subset_rfl, fischerSumSupport_eq_sum_factorial_coeff P Q Q.support subset_rfl,
        fischerSumSupport_eq_sum_factorial_coeff P' Q Q.support subset_rfl, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [coeff_add, star_add]; ring)
    (fun c P Q => by
      rw [fischerSumSupport_eq_sum_factorial_coeff (c • P) Q Q.support subset_rfl, fischerSumSupport_eq_sum_factorial_coeff P Q _ subset_rfl, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [coeff_smul, smul_eq_mul, star_mul']; simp only [Complex.star_def]; ring)
    (fun P Q Q' => by
      classical
      rw [fischerSumSupport_eq_sum_factorial_coeff P (Q + Q') (Q.support ∪ Q'.support) support_add,
        fischerSumSupport_eq_sum_factorial_coeff P Q (Q.support ∪ Q'.support) Finset.subset_union_left,
        fischerSumSupport_eq_sum_factorial_coeff P Q' (Q.support ∪ Q'.support) Finset.subset_union_right,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [coeff_add]; ring)
    (fun c P Q => by
      rw [fischerSumSupport_eq_sum_factorial_coeff P (c • Q) Q.support support_smul, fischerSumSupport_eq_sum_factorial_coeff P Q _ subset_rfl, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [coeff_smul, smul_eq_mul, RingHom.id_apply]; ring)

theorem form_eq (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : Q.support ⊆ s) :
    form P Q = ∑ α ∈ s, (fct α : ℂ) * (star (coeff α P) * coeff α Q) := fischerSumSupport_eq_sum_factorial_coeff P Q s h

theorem form_symm (P Q : MvPolynomial σ ℂ) : form P Q = star (form Q P) := by
  classical
  rw [form_eq P Q (P.support ∪ Q.support) Finset.subset_union_right,
    form_eq Q P (P.support ∪ Q.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [star_mul', mul_comm]

theorem form_self (P : MvPolynomial σ ℂ) :
    form P P = ((∑ α ∈ P.support, (fct α : ℝ) * Complex.normSq (coeff α P) : ℝ) : ℂ) := by
  rw [form_eq P P P.support subset_rfl]
  push_cast
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem form_self_nonneg (P : MvPolynomial σ ℂ) : (form P P).im = 0 ∧ 0 ≤ (form P P).re := by
  rw [form_self, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, Finset.sum_nonneg fun α _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)⟩

theorem form_self_eq_zero (P : MvPolynomial σ ℂ) (h : form P P = 0) : P = 0 := by
  rw [form_self, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun α _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))] at h
  ext α
  rw [coeff_zero]
  by_contra hne
  have := h α (mem_support_iff.mpr hne)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact (Nat.cast_ne_zero.mpr (fct_pos α).ne') h1
  · exact hne (Complex.normSq_eq_zero.mp h1)

end GlobalTheory.FockMonoForm

end

noncomputable section

namespace GlobalTheory.FockMonoForm

open MvPolynomial

variable {σ : Type} [DecidableEq σ]

theorem form_monomial (γ δ : σ →₀ ℕ) (c d : ℂ) :
    form (monomial γ c) (monomial δ d) = if γ = δ then (fct δ : ℂ) * (star c * d) else 0 := by
  rw [form_eq _ _ {δ} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial,
    if_pos rfl]
  split_ifs <;> simp

theorem form_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) : form (X v * P) Q = form P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial γ c =>
    induction Q using MvPolynomial.induction_on' with
    | monomial δ d =>
      rw [X, monomial_mul, pderiv_monomial, form_monomial, form_monomial, one_mul]
      by_cases hv : δ v = 0
      · rw [hv, if_neg]
        · simp
        · intro h
          have := congrArg (fun f : σ →₀ ℕ => f v) h
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
          omega
      · obtain ⟨α, rfl⟩ : ∃ α, δ = α + Finsupp.single v 1 :=
          ⟨δ - Finsupp.single v 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv))).symm⟩
        rw [add_tsub_cancel_right, add_comm (Finsupp.single v 1) γ]
        simp only [add_left_inj]
        rw [fct_add_single,
          Finsupp.add_apply, Finsupp.single_eq_same]
        split_ifs
        · push_cast; ring
        · rfl
    | add Q Q' hQ hQ' => rw [map_add, map_add, map_add, hQ, hQ']
  | add P P' hP hP' =>
    rw [mul_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hP, hP']

theorem form_pderiv (v : σ) (P Q : MvPolynomial σ ℂ) : form (pderiv v P) Q = form P (X v * Q) := by
  rw [form_symm, ← form_X_mul, ← form_symm]

end GlobalTheory.FockMonoForm

end

noncomputable section

namespace GlobalTheory.LowestKType

open MvPolynomial GlobalTheory.FockMonoForm GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n m : ℕ}

def FAdj (T S : Module.End ℂ (PolF D m n)) : Prop := ∀ P Q, form (T P) Q = form P (S Q)

theorem fadj_add {T S T' S' : Module.End ℂ (PolF D m n)} (h : FAdj T S) (h' : FAdj T' S') :
    FAdj (T + T') (S + S') := by
  intro P Q; simp only [LinearMap.add_apply, map_add, h P Q, h' P Q]

theorem fadj_mul {T S T' S' : Module.End ℂ (PolF D m n)} (h : FAdj T S) (h' : FAdj T' S') :
    FAdj (T * T') (S' * S) := by
  intro P Q; rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

theorem fadj_neg {T S : Module.End ℂ (PolF D m n)} (h : FAdj T S) : FAdj (-T) (-S) := by
  intro P Q; simp only [LinearMap.neg_apply, map_neg, h P Q]

theorem fadj_sum {ι : Type} (s : Finset ι) (T S : ι → Module.End ℂ (PolF D m n))
    (h : ∀ i ∈ s, FAdj (T i) (S i)) : FAdj (∑ i ∈ s, T i) (∑ i ∈ s, S i) := by
  intro P Q
  rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi P Q

theorem fadj_X {_ : DecidableEq (FVar D m n)} (v : FVar D m n) :
    FAdj (LinearMap.mulLeft ℂ (X v)) (pderiv v).toLinearMap := fun P Q => form_X_mul v P Q

theorem fadj_d {_ : DecidableEq (FVar D m n)} (v : FVar D m n) :
    FAdj (pderiv v).toLinearMap (LinearMap.mulLeft ℂ (X v)) := fun P Q => form_pderiv v P Q

theorem kop_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) :
    kop w τ a b = ∑ j, (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) a j *
      lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) b j +
        if a = b then (1 / 2 : ℂ) • 1 else 0) := by
  unfold kop fockT
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem fadj_term (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) (j : Fin n) (h : Cpt w τ a b) :
    FAdj (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) a j *
      lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) b j)
      (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) b j *
      lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) a j) := by
  classical
  unfold Cpt at h
  unfold raiO lowO sgn
  by_cases ha : (a : ℕ) < w.p τ
  · have hb := h.mp ha
    simp [ha, hb]
    have h1 := @fadj_X D n m (fun a b => Classical.propDecidable (a = b)) (τ, a, j)
    have h2 := @fadj_d D n m (fun a b => Classical.propDecidable (a = b)) (τ, b, j)
    exact fadj_mul h1 h2
  · have hb : ¬ (b : ℕ) < w.p τ := fun hb => ha (h.mpr hb)
    simp [ha, hb]
    have h1 := @fadj_d D n m (fun a b => Classical.propDecidable (a = b)) (τ, a, j)
    have h2 := @fadj_X D n m (fun a b => Classical.propDecidable (a = b)) (τ, b, j)
    exact fadj_neg (fadj_mul h1 h2)

theorem fadj_half (a b : Fin m) :
    FAdj (D := D) (n := n) (m := m) (if a = b then (1 / 2 : ℂ) • 1 else 0) (if b = a then (1 / 2 : ℂ) • 1 else 0) := by
  intro P Q
  by_cases h : a = b
  · subst h
    simp only [if_true, LinearMap.smul_apply, Module.End.one_apply, LinearMap.map_smulₛₗ₂, map_smul]
    simp [Complex.conj_ofReal, map_ofNat]
  · simp [h, Ne.symm h]

theorem fockForm_kop_adjoint : ∀ (D : D7) (n m : ℕ), ∃ B : PolF D m n →ₗ⋆[ℂ] PolF D m n →ₗ[ℂ] ℂ,
    (∀ P, (B P P).im = 0 ∧ 0 ≤ (B P P).re) ∧ (∀ P, B P P = 0 → P = 0) ∧
      ∀ (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b →
        ∀ P Q, B (GlobalTheory.LowestKType.kop w τ a b P) Q = B P (GlobalTheory.LowestKType.kop w τ b a Q) := by
  intro D n m
  refine ⟨form, form_self_nonneg, form_self_eq_zero, fun w τ a b h P Q => ?_⟩
  rw [kop_eq, kop_eq]
  exact fadj_sum _ _ _ (fun j _ => fadj_add (fadj_term w τ a b j h) (fadj_half a b)) P Q

end GlobalTheory.LowestKType

end
