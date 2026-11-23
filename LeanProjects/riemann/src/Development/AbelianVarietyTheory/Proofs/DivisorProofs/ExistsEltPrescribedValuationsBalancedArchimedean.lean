import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem sum_embeddings_eq_sum_places {K : Type} [Field K] [NumberField K] (g : (K →+* ℂ) → ℝ)
    (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ, g σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * g w.embedding := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
      rw [this, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

theorem t_embedding_mk {K : Type} [Field K] (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (σ : K →+* ℂ) : t (InfinitePlace.mk σ).embedding = t σ := by
  rcases embedding_mk_eq σ with h | h
  · rw [h]
  · have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
      RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
    rw [h, this, ht]

theorem minkowskiBound_eq_absNorm_mul {K : Type} [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    minkowskiBound K I = ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      minkowskiBound K 1 := by
  unfold minkowskiBound
  rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_fractionalIdealLatticeBasis]
  simp [mul_assoc]

end GlobalTheory.CovHt

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem exists_elt_balanced : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧
      (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  intro K _ _ e t ht

  have hNpos : ∀ la : HeightOneSpectrum (𝓞 K), (0 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hNone : ∀ la : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have h := hNpos la
    have : (1 : ℕ) ≤ Ideal.absNorm la.asIdeal := by exact_mod_cast h
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set S : ℝ := e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ) with hS
  set A : ℝ := ∑ la ∈ e.support, Real.log (Ideal.absNorm la.asIdeal : ℝ) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun la _ => Real.log_nonneg (hNone la)
  set V0 : ℝ := (minkowskiBound K 1).toReal with hV0
  have hV0nn : 0 ≤ V0 := ENNReal.toReal_nonneg
  set c : ℝ := |Real.log V0| + A + 1 with hc
  refine ⟨c, fun τ => ?_⟩
  set m : HeightOneSpectrum (𝓞 K) → ℤ := fun la => ⌈(τ : ℝ) * e la⌉ with hm
  have hm0 : ∀ la, la ∉ e.support → m la = 0 := by
    intro la hla
    rw [Finsupp.notMem_support_iff] at hla
    simp [hm, hla]
  have hmfin : ∀ᶠ v in Filter.cofinite, m v = 0 := by
    rw [Filter.eventually_cofinite]
    refine e.support.finite_toSet.subset fun v hv => ?_
    by_contra h
    exact hv (hm0 v h)
  set I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ v, GroundTheory.Global.primeIdealUnit v ^ m v with hI
  have hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = m v :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow m hmfin

  have hnorm : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
      ∏ la ∈ e.support, (Ideal.absNorm la.asIdeal : ℝ) ^ m la := by
    rw [hI, GroundTheory.Global.coe_finprod_primeIdealUnit_zpow m hmfin,
      finprod_eq_prod_of_mulSupport_subset (s := e.support)]
    · rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun la _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    · intro v hv
      by_contra h
      exact hv (by simp [hm0 v h])
  have hnormle : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) ≤ Real.exp (τ * S + A) := by
    rw [hnorm]
    have hS' : S = ∑ la ∈ e.support, e la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := rfl
    rw [hS', hA, Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun la _ => by positivity) fun la _ => ?_
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hNpos la)]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((m la : ℤ) : ℝ) ≤ τ * e la + 1 := (Int.ceil_lt_add_one _).le
    have h2 := Real.log_nonneg (hNone la)
    nlinarith

  set g : InfinitePlace K → ℝ := fun w => (τ : ℝ) * (cost e t - t w.embedding) + c with hg
  set f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (g w), (Real.exp_pos _).le⟩ with hf
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * g w = τ * S + (Module.finrank ℚ K : ℝ) * c := by
    have h := sum_embeddings_eq_sum_places (K := K) (fun σ => (τ : ℝ) * (cost e t - t σ) + c)
      (fun σ => by simp only [ht])
    rw [show (∑ w : InfinitePlace K, (w.mult : ℝ) * g w) =
        ∑ w : InfinitePlace K, (w.mult : ℝ) * ((τ : ℝ) * (cost e t - t w.embedding) + c) from rfl, ← h]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, nsmul_eq_mul]
    have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by positivity
    have hcost : (Module.finrank ℚ K : ℝ) * cost e t = S + ∑ σ, t σ := by
      rw [cost, mul_div_cancel₀ _ hn0]
    rw [hcost]; ring
  have hprod : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
    rw [NNReal.coe_prod, ← hsum, Real.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [NNReal.coe_pow, Real.exp_nat_mul]
    rfl
  have hmink : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume, minkowskiBound_eq_absNorm_mul]
    have h1 : minkowskiBound K 1 = ENNReal.ofReal V0 := (ENNReal.ofReal_toReal (minkowskiBound_lt_top K 1).ne).symm
    rw [h1, ← ENNReal.ofReal_mul (by
      rw [hnorm]; exact Finset.prod_nonneg fun la _ => by positivity)]
    refine lt_of_lt_of_le ?_ (le_mul_of_one_le_left zero_le' (by exact_mod_cast one_le_convexBodyLTFactor K))
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by rw [hprod]; positivity), hprod]
    have hV : V0 ≤ Real.exp |Real.log V0| := by
      rcases hV0nn.eq_or_lt with h | h
      · rw [← h]; positivity
      · calc V0 = Real.exp (Real.log V0) := (Real.exp_log h).symm
          _ ≤ Real.exp |Real.log V0| := Real.exp_le_exp.2 (le_abs_self _)
    calc ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) * V0
        ≤ Real.exp (τ * S + A) * Real.exp |Real.log V0| :=
          mul_le_mul hnormle hV hV0nn (Real.exp_pos _).le
      _ = Real.exp (τ * S + (A + |Real.log V0|)) := by rw [← Real.exp_add]; ring_nf
      _ < Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
          refine Real.exp_lt_exp.2 ?_
          have hc0 : 0 ≤ c := by positivity
          nlinarith
  obtain ⟨α, hαI, hα0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I hmink
  refine ⟨α, hα0, fun la => ?_, fun σ => ?_⟩
  · have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ α ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0
    have hle := FractionalIdeal.count_mono K la hsp (FractionalIdeal.spanSingleton_le_iff_mem.2 hαI)
    rw [hcount, GroundTheory.Global.count_spanSingleton la hα0] at hle
    have hv : vLa la α = -WithZero.log (la.valuation K α) := rfl
    calc (τ : ℝ) * e la ≤ (m la : ℝ) := Int.le_ceil _
      _ ≤ (vLa la α : ℝ) := by rw [hv]; exact_mod_cast hle
  · have h := hlt (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h
    have hpos : 0 < ‖σ α‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hα0)
    have : Real.log ‖σ α‖ ≤ Real.log (f (InfinitePlace.mk σ) : ℝ) := Real.log_le_log hpos h.le
    rw [show ((f (InfinitePlace.mk σ)) : ℝ) = Real.exp (g (InfinitePlace.mk σ)) from rfl, Real.log_exp] at this
    rw [hg] at this
    simp only [t_embedding_mk t ht σ] at this
    exact this

end GlobalTheory.CovHt
