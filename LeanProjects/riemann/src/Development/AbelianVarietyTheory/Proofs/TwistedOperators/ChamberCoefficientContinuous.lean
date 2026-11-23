import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger

noncomputable section

open MeasureTheory GlobalTheory.Chamber Finset
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FamCont

theorem deriv_pow_succ_mul {g : ℝ → ℂ} (hg : Differentiable ℝ g) (m : ℕ) :
    deriv (fun t : ℝ => (t : ℂ) ^ (m + 1) * g t) =
      fun t : ℝ => (t : ℂ) ^ m * (((m : ℂ) + 1) * g t + (t : ℂ) * deriv g t) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m) t := by
    simpa using (hasDerivAt_pow (m + 1) (t : ℂ)).comp_ofReal
  have h3 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (m + 1) * g t)
      (((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m * g t + (t : ℂ) ^ (m + 1) * deriv g t) t := h1.mul (hg t).hasDerivAt
  rw [h3.deriv]
  push_cast; ring

theorem contDiff_linear_deriv_combination {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (a : ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => a * g t + (t : ℂ) * deriv g t) := by
  have hd := (contDiff_infty_iff_deriv.1 hg).2
  exact (contDiff_const.mul hg).add (Complex.ofRealCLM.contDiff.mul hd)

theorem iteratedDeriv_pow_mul (n : ℕ) : ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g →
    iteratedDeriv n (fun t : ℝ => (t : ℂ) ^ n * g t) 0 = n.factorial * g 0 := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [iteratedDeriv_succ', deriv_pow_succ_mul (hg.differentiable (by simp)), ih _ (contDiff_linear_deriv_combination hg _)]
    simp [Nat.factorial_succ]
    ring

theorem iteratedDeriv_sum_exp {ι : Type} (s : Finset ι) (e c : ι → ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ∑ i ∈ s, e i * Complex.exp (c i * t)) =
      fun t : ℝ => ∑ i ∈ s, e i * c i ^ n * Complex.exp (c i * (t : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : ∀ i ∈ s, HasDerivAt (fun t : ℝ => e i * c i ^ n * Complex.exp (c i * t))
        (e i * c i ^ (n + 1) * Complex.exp (c i * t)) t := fun i _ => by
      have h1 : HasDerivAt (fun t : ℝ => c i * (t : ℂ)) (c i) t := by
        simpa using ((hasDerivAt_id (t : ℂ)).const_mul (c i)).comp_ofReal
      have h2 : HasDerivAt (fun t : ℝ => e i * c i ^ n * Complex.exp (c i * t))
          (e i * c i ^ n * (Complex.exp (c i * t) * c i)) t := h1.cexp.const_mul (e i * c i ^ n)
      exact h2.congr_deriv (by ring)
    have hs := HasDerivAt.sum h
    rw [Finset.sum_fn] at hs
    exact hs.deriv

theorem card_eq_finrank {k : ℕ} {P : Finset (SV k)} (h : IsPar P) : Module.finrank ℝ (aP P) = P.card := by
  have li : LinearIndependent ℝ (fun u : (P : Set (SV k)) => vec (k := k) u) := by
    rw [linearIndependent_iff_notMem_span]
    rintro ⟨u, hu⟩
    have h' := h.vec_notMem hu
    convert h' using 3
    rw [aP]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and, Subtype.exists,
      Finset.mem_coe, Finset.mem_erase, Subtype.mk.injEq]
    constructor
    · rintro ⟨a, ha, hne, rfl⟩; exact ⟨a, ⟨hne, ha⟩, rfl⟩
    · rintro ⟨a, ⟨hne, ha⟩, rfl⟩; exact ⟨a, ha, hne, rfl⟩
  have := finrank_span_eq_card li
  rw [aP, Set.image_eq_range, this]
  convert Fintype.card_coe P
  simp

theorem isGMFam_expFam {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {X : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X) :
    IsGMFam 𝔞 (expFam X) := by
  intro P hP
  refine ⟨?_, fun R hR l => ?_⟩
  · unfold expFam eL
    exact Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)))
  · simp only [expFam, eL]
    rw [hX P hP R hR, pr, Submodule.inner_starProjection_left_eq_right]

theorem smul_mem_generic {k : ℕ} {l : A0 k} (hl : l ∈ generic k) {t : ℝ} (ht : t ≠ 0) : t • l ∈ generic k := by
  intro P hP R hR u hu
  rw [real_inner_smul_left]
  exact mul_ne_zero ht (hl P hP R hR u hu)

theorem card_sdiff_of_mem_parP {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} {Q P : Finset (SV k)} (hP : P ∈ parP 𝔞 Q) :
    (P \ Q).card = Module.finrank ℝ 𝔞 - Q.card := by
  obtain ⟨hP1, hP2, hP3⟩ := mem_parP.1 hP
  rw [card_sdiff_of_subset hP3, ← card_eq_finrank hP1, hP2]

theorem eps_smul {k : ℕ} (P Q : Finset (SV k)) (l : A0 k) (t : ℝ) :
    eps P Q (t • l) = ((t : ℂ) ^ (P \ Q).card)⁻¹ * eps P Q l := by
  have e1 : ∀ a : ℂ, (Complex.I * ((t : ℂ) * a))⁻¹ = (t : ℂ)⁻¹ * (Complex.I * a)⁻¹ := fun a => by
    rw [mul_left_comm, mul_inv]
  simp only [eps, epsOf, real_inner_smul_left, Complex.ofReal_mul]
  simp_rw [e1, prod_mul_distrib, prod_const, inv_pow]
  ring

theorem cM_expFam_zero (hFS : FamilySmooth) {k : ℕ} {𝔞 : Submodule ℝ (A0 k)} (h𝔞 : IsLevi 𝔞) {Q : Finset (SV k)}
    (hQ : Q ∈ parF 𝔞 ∅) {X : Finset (SV k) → A0 k} (hX : IsOrth 𝔞 X) {l₀ : A0 k} (hl₀ : l₀ ∈ generic k) :
    cM 𝔞 Q (expFam X) 0 = (∑ P ∈ parP 𝔞 Q, eps P Q l₀ *
      (Complex.I * (⟪l₀, X P⟫_ℝ : ℂ)) ^ (Module.finrank ℝ 𝔞 - Q.card)) / (Module.finrank ℝ 𝔞 - Q.card).factorial := by
  set n := Module.finrank ℝ 𝔞 - Q.card
  obtain ⟨⟨hsm, heq⟩, -⟩ := hFS k 𝔞 h𝔞 _ (isGMFam_expFam hX) Q hQ
  set f : ℝ → ℂ := fun t => cM 𝔞 Q (expFam X) (t • l₀) with hfdef
  have hf : ContDiff ℝ ∞ f := hsm.comp (contDiff_id.smul contDiff_const)
  have hfun : (fun t : ℝ => (t : ℂ) ^ n * f t) = fun t : ℝ => ∑ P ∈ parP 𝔞 Q,
      eps P Q l₀ * Complex.exp ((Complex.I * (⟪l₀, X P⟫_ℝ : ℂ)) * (t : ℂ)) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℝ))
      ((Complex.continuous_ofReal.pow n).mul hf.continuous)
      (continuous_finset_sum _ fun P _ => continuous_const.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) ?_
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [hfdef]
    rw [heq (smul_mem_generic hl₀ ht), sumM, mul_sum]
    refine sum_congr rfl fun P hP => ?_
    rw [eps_smul, card_sdiff_of_mem_parP hP, expFam, eL, real_inner_smul_left, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht)), one_mul]
    congr 2
    push_cast
    ring
  have h1 := iteratedDeriv_pow_mul n f hf
  rw [hfun, iteratedDeriv_sum_exp] at h1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hfdef, zero_smul] at h1
  rw [h1, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))]

theorem continuous_cM_expFam_zero : FamilySmooth → ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ Q ∈ parF 𝔞 ∅,
    ∀ (Z : Type) [TopologicalSpace Z] (X : Z → Finset (SV k) → A0 k), (∀ z, IsOrth 𝔞 (X z)) →
    (∀ P ∈ parP 𝔞 Q, Continuous fun z => X z P) → Continuous fun z => cM 𝔞 Q (expFam (X z)) 0 := by
  intro hFS k 𝔞 h𝔞 Q hQ Z _ X hX hc
  obtain ⟨l₀, hl₀⟩ : (generic k).Nonempty := dense_generic.nonempty
  simp_rw [cM_expFam_zero hFS h𝔞 hQ (hX _) hl₀]
  refine Continuous.div_const (continuous_finset_sum _ fun P hP => ?_) _
  exact continuous_const.mul ((continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.inner (hc P hP)))).pow _)

end GlobalTheory.FamCont
