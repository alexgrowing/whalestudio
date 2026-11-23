import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

section General

variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)

def gaussNormOf (f : MvPolynomial ι R) : ℝ :=
  let s : NNReal := f.support.sup fun m => ⟨w (f.coeff m), w.nonneg _⟩
  (s : ℝ)

theorem gaussNormOf_def (f : MvPolynomial ι R) :
    gaussNormOf w f = (((f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) : NNReal) : ℝ) :=
  rfl

theorem gaussNormOf_nonneg (f : MvPolynomial ι R) : 0 ≤ gaussNormOf w f := NNReal.coe_nonneg _

theorem le_gaussNormOf (f : MvPolynomial ι R) (m : ι →₀ ℕ) : w (f.coeff m) ≤ gaussNormOf w f := by
  by_cases hm : m ∈ f.support
  · have h : (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) ≤
        f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) :=
      Finset.le_sup (f := fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) hm
    rw [gaussNormOf_def]
    exact NNReal.coe_le_coe.mpr h
  · rw [notMem_support_iff.mp hm, map_zero]
    exact gaussNormOf_nonneg w f

theorem gaussNormOf_le {f : MvPolynomial ι R} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m, w (f.coeff m) ≤ r) : gaussNormOf w f ≤ r := by
  have h' : (f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) ≤ ⟨r, hr⟩ :=
    Finset.sup_le fun m _ => h m
  rw [gaussNormOf_def]
  exact NNReal.coe_le_coe.mpr h'

theorem exists_gaussNormOf_eq {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ m ∈ f.support, gaussNormOf w f = w (f.coeff m) := by
  obtain ⟨m, hm, h⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal))
  refine ⟨m, hm, ?_⟩
  rw [gaussNormOf_def]
  exact congrArg Subtype.val h

theorem gaussNormOf_pos {f : MvPolynomial ι R} (hf : f ≠ 0) : 0 < gaussNormOf w f := by
  obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
  rw [h]
  exact w.pos (mem_support_iff.mp hm)

theorem gaussNormOf_zero : gaussNormOf w (0 : MvPolynomial ι R) = 0 :=
  le_antisymm (gaussNormOf_le w le_rfl fun m => by simp) (gaussNormOf_nonneg w 0)

theorem gaussNormOf_C (c : R) : gaussNormOf w (C c : MvPolynomial ι R) = w c := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (w.nonneg c) fun m => ?_
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · rw [map_zero]
      exact w.nonneg c
  · simpa using le_gaussNormOf w (C c : MvPolynomial ι R) 0

variable {w}

theorem gaussNormOf_mul_le (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) ≤ gaussNormOf w f * gaussNormOf w g := by
  classical
  refine gaussNormOf_le w (mul_nonneg (gaussNormOf_nonneg w f) (gaussNormOf_nonneg w g)) fun m => ?_
  rw [coeff_mul]
  refine (hna.apply_sum_le_sup (s := Finset.HasAntidiagonal.antidiagonal m) ⟨(0, m), by simp⟩).trans ?_
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [map_mul]
  exact mul_le_mul (le_gaussNormOf w f _) (le_gaussNormOf w g _) (w.nonneg _)
    (gaussNormOf_nonneg w f)

theorem le_gaussNormOf_mul (hna : IsNonarchimedean w) {f g : MvPolynomial ι R} (hf : f ≠ 0)
    (hg : g ≠ 0) : gaussNormOf w f * gaussNormOf w g ≤ gaussNormOf w (f * g) := by
  classical
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hNf := gaussNormOf_pos w hf
  have hNg := gaussNormOf_pos w hg
  obtain ⟨i, hi, hmin_i⟩ :=
    (f.support.filter fun a => w (f.coeff a) = gaussNormOf w f).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  obtain ⟨j, hj, hmin_j⟩ :=
    (g.support.filter fun a => w (g.coeff a) = gaussNormOf w g).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hg
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  have hi' : w (f.coeff i) = gaussNormOf w f := (Finset.mem_filter.mp hi).2
  have hj' : w (g.coeff j) = gaussNormOf w g := (Finset.mem_filter.mp hj).2
  have ltf : ∀ a, toLex a < toLex i → w (f.coeff a) < gaussNormOf w f := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w f a) fun h => ?_
    have ha' : a ∈ f.support.filter fun a => w (f.coeff a) = gaussNormOf w f := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNf.ne h
    exact absurd (hmin_i a ha') (not_le.mpr ha)
  have ltg : ∀ a, toLex a < toLex j → w (g.coeff a) < gaussNormOf w g := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w g a) fun h => ?_
    have ha' : a ∈ g.support.filter fun a => w (g.coeff a) = gaussNormOf w g := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNg.ne h
    exact absurd (hmin_j a ha') (not_le.mpr ha)
  have key : w ((f * g).coeff (i + j)) = gaussNormOf w f * gaussNormOf w g := by
    rw [coeff_mul]
    have hk : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [hna.apply_sum_eq_of_lt (fun a => (w.map_neg a).symm) hk ?_, map_mul, hi', hj']
    intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_mul, map_mul, hi', hj']
    rcases lt_trichotomy (toLex p.1) (toLex i) with h | h | h
    · calc w (f.coeff p.1) * w (g.coeff p.2) ≤ w (f.coeff p.1) * gaussNormOf w g :=
            mul_le_mul_of_nonneg_left (le_gaussNormOf w g _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_right (ltf _ h) hNg
    · have h1 : p.1 = i := toLex.injective h
      have h2 : p.2 = j := by
        rw [h1] at hp
        exact add_left_cancel hp
      exact absurd (Prod.ext h1 h2) hne
    · have h2 : toLex p.2 < toLex j := by
        by_contra hc
        rw [not_lt] at hc
        have hlt : toLex i + toLex j < toLex p.1 + toLex p.2 := add_lt_add_of_lt_of_le h hc
        have e : toLex p.1 + toLex p.2 = toLex i + toLex j := by
          rw [← toLex_add, ← toLex_add, hp]
        rw [e] at hlt
        exact lt_irrefl _ hlt
      calc w (f.coeff p.1) * w (g.coeff p.2) ≤ gaussNormOf w f * w (g.coeff p.2) :=
            mul_le_mul_of_nonneg_right (le_gaussNormOf w f _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_left (ltg _ h2) hNf
  rw [← key]
  exact le_gaussNormOf w _ _

theorem gaussNormOf_mul (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) = gaussNormOf w f * gaussNormOf w g := by
  by_cases hf : f = 0
  · simp [hf, gaussNormOf_zero]
  by_cases hg : g = 0
  · simp [hg, gaussNormOf_zero]
  exact le_antisymm (gaussNormOf_mul_le hna f g) (le_gaussNormOf_mul hna hf hg)

end General

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_eq_gaussNormOf (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) :
    gaussNorm v f = gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) f := rfl

theorem gaussNorm_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f g : MvPolynomial ι K) : gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g :=
  gaussNormOf_mul (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v) f g

theorem gaussNorm_C (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K) :
    gaussNorm v (C c : MvPolynomial ι K) = NumberField.HeightOneSpectrum.adicAbv K v c :=
  gaussNormOf_C _ c

theorem gaussNorm_C_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K)
    (f : MvPolynomial ι K) :
    gaussNorm v (C c * f) = NumberField.HeightOneSpectrum.adicAbv K v c * gaussNorm v f := by
  rw [gaussNorm_mul, gaussNorm_C]

theorem gaussNorm_nonneg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) : 0 ≤ gaussNorm v f := gaussNormOf_nonneg _ f

theorem gaussNorm_pos (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    {f : MvPolynomial ι K} (hf : f ≠ 0) : 0 < gaussNorm v f := gaussNormOf_pos _ hf

theorem adicAbv_mulSupport_finite {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x).Finite := by
  have h := FinitePlace.hasFiniteMulSupport hx
  have e : (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x) =
      FinitePlace.equivHeightOneSpectrum.symm ⁻¹'
        (Function.mulSupport fun w : FinitePlace K => w x) := by
    ext v
    simp only [Function.mem_mulSupport, Set.mem_preimage,
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e]
  exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h

theorem log_gaussNorm_support_finite {ι : Type*} {f : MvPolynomial ι K} (hf : f ≠ 0) :
    (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v f)).Finite := by
  classical
  refine (Set.Finite.biUnion (s := (f.support : Set (ι →₀ ℕ))) f.support.finite_toSet
    fun m hm => adicAbv_mulSupport_finite (K := K) (mem_support_iff.mp hm)).subset ?_
  intro v hv
  rw [Function.mem_support] at hv
  by_contra hc
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hc
  apply hv
  have h1 : gaussNorm v f = 1 := by
    apply le_antisymm
    · refine gaussNormOf_le _ zero_le_one fun m => ?_
      by_cases hm : m ∈ f.support
      · exact (hc m hm).le
      · rw [notMem_support_iff.mp hm, map_zero]
        exact zero_le_one
    · obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
      rw [gaussNorm_eq_gaussNormOf, h, hc m hm]
  rw [h1, Real.log_one]

end NumberField

theorem gaussLemma : GaussLemma.Statement := fun _K _ _ v _ι f g => gaussNorm_mul v f g

end

end GroundTheory.Heights₂.Heights
