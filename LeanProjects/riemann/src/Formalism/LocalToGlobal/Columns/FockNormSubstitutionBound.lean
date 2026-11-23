import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound

open MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section General

variable {σ : Type}

theorem fockL_self (f : MvPolynomial σ ℂ) : fockL f f = (fockN f : ℂ) := by
  rw [fockL_apply]
  unfold fockS fockN
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem fockN_eq_sum (f : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) (h : f.support ⊆ S) :
    fockN f = ∑ m ∈ S, ‖coeff m f‖ ^ 2 * (mfact m : ℝ) := by
  unfold fockN
  refine Finset.sum_subset h fun m _ hm => ?_
  rw [notMem_support_iff.1 hm]
  simp

theorem cauchy_schwarz_finite_sum {β : Type} [Fintype β] (c z : β → ℂ) : ‖∑ b, c b * z b‖ ^ 2 ≤ (∑ b, ‖c b‖ ^ 2) * ∑ b, ‖z b‖ ^ 2 := by
  have h1 : ‖∑ b, c b * z b‖ ≤ ∑ b, ‖c b‖ * ‖z b‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖c b‖) (fun b => ‖z b‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem fockN_lin_le {β : Type} [Fintype β] (c : β → ℂ) (G : β → MvPolynomial σ ℂ) :
    fockN (∑ b, C (c b) * G b) ≤ (∑ b, ‖c b‖ ^ 2) * ∑ b, fockN (G b) := by
  classical
  set S : Finset (σ →₀ ℕ) := (∑ b, C (c b) * G b).support ∪ Finset.univ.biUnion fun b => (G b).support with hS
  rw [fockN_eq_sum _ S Finset.subset_union_left]
  have hG : ∀ b, fockN (G b) = ∑ m ∈ S, ‖coeff m (G b)‖ ^ 2 * (mfact m : ℝ) := fun b =>
    fockN_eq_sum _ S ((Finset.subset_biUnion_of_mem (fun b => (G b).support) (Finset.mem_univ b)).trans Finset.subset_union_right)
  simp only [hG]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [coeff_sum]
  simp only [coeff_C_mul]
  exact cauchy_schwarz_finite_sum c fun b => coeff m (G b)

variable [DecidableEq σ]

theorem coeff_X_mul_pderiv_columns (v : σ) (F : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (X v * pderiv v F) = (m v : ℂ) * coeff m F := by
  induction F using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, coeff_X_mul', coeff_monomial, coeff_monomial]
    by_cases hv : v ∈ m.support
    · have h1 : 1 ≤ m v := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
      have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h1)
      rw [if_pos hv]
      by_cases hu : u = m
      · subst hu
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hu, mul_zero]
        by_cases h2 : u - Finsupp.single v 1 = m - Finsupp.single v 1
        · rw [if_pos h2]
          by_cases h3 : u v = 0
          · rw [h3]; simp
          · exfalso
            apply hu
            have hu' : u - Finsupp.single v 1 + Finsupp.single v 1 = u :=
              tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h3))
            rw [← hu', h2, hm]
        · rw [if_neg h2]
    · rw [if_neg hv, Finsupp.notMem_support_iff.1 hv]
      simp
  | add p q hp hq => rw [map_add, mul_add, coeff_add, coeff_add, hp, hq]; ring

theorem coeff_pderiv_eq_coeff_add_single_mul (v : σ) (F : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (pderiv v F) = coeff (m + Finsupp.single v 1) F * ((m v : ℂ) + 1) := by
  have h := coeff_X_mul_pderiv_columns v F (m + Finsupp.single v 1)
  rw [coeff_X_mul', if_pos (by simp), add_tsub_cancel_right] at h
  rw [h]
  simp
  ring

end General

section Block

variable {ι : Type} [Fintype ι] {n : ℕ}

def blkE (τ : ι) (F : MvPolynomial (ι × Fin n × Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∑ a, ∑ t, X (τ, a, t) * pderiv (τ, a, t) F

def BlockHomogeneous (F : MvPolynomial (ι × Fin n × Fin n) ℂ) (d : ι → ℕ) : Prop :=
  ∀ m, coeff m F ≠ 0 → ∀ τ, ∑ a, ∑ s, m (τ, a, s) = d τ

theorem blkE_of_hom {F : MvPolynomial (ι × Fin n × Fin n) ℂ} {d : ι → ℕ} (h : BlockHomogeneous F d) (τ : ι) : blkE τ F = (d τ : ℂ) • F := by
  classical
  ext m
  unfold blkE
  rw [coeff_sum, coeff_smul, smul_eq_mul]
  simp only [coeff_sum, coeff_X_mul_pderiv_columns]
  simp only [← Finset.sum_mul]
  by_cases h0 : coeff m F = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [← h m h0 τ]
    push_cast
    rfl

theorem blkE_blockAct (U : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (F : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blkE τ (Formalism.GradedWeylDivisibility.blockAct ℂ U F) = Formalism.GradedWeylDivisibility.blockAct ℂ U (blkE τ F) := by
  classical
  unfold blkE
  simp only [map_sum, map_mul, blockAct_X, pderiv_blockAct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem fockN_euler (τ : ι) (G : MvPolynomial (ι × Fin n × Fin n) ℂ) (c : ℕ) (hE : blkE τ G = (c : ℂ) • G) :
    ∑ a, ∑ t, fockN (pderiv (τ, a, t) G) = (c : ℝ) * fockN G := by
  classical
  have : ((∑ a, ∑ t, fockN (pderiv (τ, a, t) G) : ℝ) : ℂ) = (((c : ℝ) * fockN G : ℝ) : ℂ) := by
    push_cast
    simp only [← fockL_self, fockL_pderiv_X]
    have e : ∑ a, ∑ t, fockL G (X (τ, a, t) * pderiv (τ, a, t) G) = fockL G (blkE τ G) := by
      unfold blkE
      simp only [map_sum]
    rw [e, hE, map_smul, smul_eq_mul]
  exact_mod_cast this

theorem blkHom_pderiv {F : MvPolynomial (ι × Fin n × Fin n) ℂ} {d : ι → ℕ} [DecidableEq ι] (h : BlockHomogeneous F d) (τ₀ : ι) (e : ℕ) (he : d τ₀ = e + 1)
    (b t : Fin n) : BlockHomogeneous (pderiv (τ₀, b, t) F) (Function.update d τ₀ e) := by
  intro m hm τ
  rw [coeff_pderiv_eq_coeff_add_single_mul] at hm
  have h1 := h _ (left_ne_zero_of_mul hm) τ
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1
  by_cases hτ : τ = τ₀
  · subst hτ
    rw [Function.update_self]
    have h2 : ∑ a, ∑ s, (Finsupp.single (τ, b, t) 1 : (ι × Fin n × Fin n) →₀ ℕ) (τ, a, s) = 1 := by
      rw [Finset.sum_eq_single b, Finset.sum_eq_single t]
      · simp
      · intro s _ hs
        rw [Finsupp.single_apply, if_neg]
        intro h'
        exact hs (by simpa using (congrArg (fun z : ι × Fin n × Fin n => z.2.2) h').symm)
      · intro h'; exact absurd (Finset.mem_univ _) h'
      · intro a _ ha
        refine Finset.sum_eq_zero fun s _ => ?_
        rw [Finsupp.single_apply, if_neg]
        intro h'
        exact ha (by simpa using (congrArg (fun z : ι × Fin n × Fin n => z.2.1) h').symm)
      · intro h'; exact absurd (Finset.mem_univ _) h'
    omega
  · rw [Function.update_of_ne hτ]
    have h2 : ∑ a, ∑ s, (Finsupp.single (τ₀, b, t) 1 : (ι × Fin n × Fin n) →₀ ℕ) (τ, a, s) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun s _ => ?_
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact hτ (by simpa using (congrArg (fun z : ι × Fin n × Fin n => z.1) h').symm)
    omega

theorem fock_norm_substitution_bound (U : ι → Matrix (Fin n) (Fin n) ℂ) : ∀ (D : ℕ) (d : ι → ℕ), ∑ τ, d τ = D →
    ∀ F : MvPolynomial (ι × Fin n × Fin n) ℂ, BlockHomogeneous F d →
      fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U F) ≤ (∏ τ, hsN (U τ) ^ d τ) * fockN F := by
  classical
  intro D
  induction D with
  | zero =>
    intro d hd F hF
    have hd0 : ∀ τ, d τ = 0 := fun τ => (Finset.sum_eq_zero_iff.1 hd) τ (Finset.mem_univ _)
    have hC : F = C (coeff 0 F) := by
      ext m
      rw [coeff_C]
      by_cases hm : 0 = m
      · rw [if_pos hm, hm]
      · rw [if_neg hm]
        by_contra h0
        apply hm
        ext v
        obtain ⟨τ, a, s⟩ := v
        have h1 := hF m h0 τ
        rw [hd0 τ, Finset.sum_eq_zero_iff] at h1
        have h2 := h1 a (Finset.mem_univ _)
        rw [Finset.sum_eq_zero_iff] at h2
        exact (h2 s (Finset.mem_univ _)).symm
    rw [hC, algHom_C]
    simp [hd0]
  | succ D ih =>
    intro d hd F hF
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, d τ₀ ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero fun τ _ => h τ] at hd
      omega
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hτ₀
    set d' : ι → ℕ := Function.update d τ₀ e with hd'
    have hsum : ∑ τ, d' τ = D := by
      have h1 := Finset.sum_update_of_mem (Finset.mem_univ τ₀) d e
      have h2 := Finset.add_sum_erase Finset.univ d (Finset.mem_univ τ₀)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      rw [hd', h1]
      omega
    have hprod : ∏ τ, hsN (U τ) ^ d τ = hsN (U τ₀) * ∏ τ, hsN (U τ) ^ d' τ := by
      rw [← Finset.mul_prod_erase Finset.univ (fun τ => hsN (U τ) ^ d τ) (Finset.mem_univ τ₀),
        ← Finset.mul_prod_erase Finset.univ (fun τ => hsN (U τ) ^ d' τ) (Finset.mem_univ τ₀)]
      have e1 : ∏ τ ∈ Finset.univ.erase τ₀, hsN (U τ) ^ d' τ = ∏ τ ∈ Finset.univ.erase τ₀, hsN (U τ) ^ d τ :=
        Finset.prod_congr rfl fun τ hτ => by rw [hd', Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
      rw [e1, hd', Function.update_self, he, pow_succ]
      ring
    set G := Formalism.GradedWeylDivisibility.blockAct ℂ U F with hG
    have hEG : blkE τ₀ G = ((e + 1 : ℕ) : ℂ) • G := by
      rw [hG, blkE_blockAct, blkE_of_hom hF τ₀, map_smul, he]
    have h1 := fockN_euler τ₀ G (e + 1) hEG
    have h2 := fockN_euler τ₀ F (e + 1) (by rw [blkE_of_hom hF τ₀, he])
    have h3 : ∀ a t, fockN (pderiv (τ₀, a, t) G) ≤
        (∑ b, ‖U τ₀ b a‖ ^ 2) * ∑ b, fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U (pderiv (τ₀, b, t) F)) := by
      intro a t
      rw [hG, pderiv_blockAct]
      exact fockN_lin_le _ _
    have h4 : ∀ b t, fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U (pderiv (τ₀, b, t) F)) ≤ (∏ τ, hsN (U τ) ^ d' τ) * fockN (pderiv (τ₀, b, t) F) :=
      fun b t => ih d' hsum _ (blkHom_pderiv hF τ₀ e he b t)
    have hP : 0 ≤ ∏ τ, hsN (U τ) ^ d' τ := Finset.prod_nonneg fun τ _ => pow_nonneg (hsN_nonneg _) _
    have h5 : ((e + 1 : ℕ) : ℝ) * fockN G ≤ ((e + 1 : ℕ) : ℝ) * ((∏ τ, hsN (U τ) ^ d τ) * fockN F) := by
      rw [← h1]
      calc ∑ a, ∑ t, fockN (pderiv (τ₀, a, t) G)
          ≤ ∑ a, ∑ t, (∑ b, ‖U τ₀ b a‖ ^ 2) * ∑ b, (∏ τ, hsN (U τ) ^ d' τ) * fockN (pderiv (τ₀, b, t) F) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun t _ => (h3 a t).trans
              (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => h4 b t) (Finset.sum_nonneg fun _ _ => by positivity))
        _ = (∑ a, ∑ b, ‖U τ₀ b a‖ ^ 2) * ((∏ τ, hsN (U τ) ^ d' τ) * ∑ t, ∑ b, fockN (pderiv (τ₀, b, t) F)) := by
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
        _ = hsN (U τ₀) * ((∏ τ, hsN (U τ) ^ d' τ) * ∑ b, ∑ t, fockN (pderiv (τ₀, b, t) F)) := by
            unfold hsN
            rw [Finset.sum_comm, Finset.sum_comm (f := fun t b => fockN (pderiv (τ₀, b, t) F))]
        _ = _ := by rw [h2, hprod]; ring
    exact le_of_mul_le_mul_left h5 (by positivity)

theorem fockSubNorm : FockSubNorm := fun ι _ n U d F hF => fock_norm_substitution_bound U _ d rfl F hF

end Block

end Formalism.L2.Col
