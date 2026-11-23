import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing GlobalTheory.ArcQ

namespace GlobalTheory.ArcFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma trace_cc (z : E) : Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

lemma eq_zero_of_trace_mul (z : E) (h : ∀ β : 𝓞 E, Algebra.trace ℚ E ((β : E) * z) = 0) : z = 0 := by
  have := eq_zero_of_trace (cc z) fun β => by rw [← cc_mul, trace_cc, h]
  simpa using this

lemma map_cc (τ : E →+* ℂ) (z : E) : τ (cc z) = starRingEnd ℂ (τ z) :=
  IsCMField.complexEmbedding_complexConj E τ z

lemma re_nonneg_of_trace (s : E)
    (h : ∀ a : 𝓞 E, 0 ≤ Algebra.trace ℚ E (s * (a : E) * cc (a : E))) (τ : E →+* ℂ) : 0 ≤ (τ s).re := by
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit E (InfinitePlace.mk τ)
  have hlt : ∀ w : InfinitePlace E, w ≠ InfinitePlace.mk τ → w ((u : 𝓞 E) : E) < 1 := fun w hw =>
    (Real.log_neg_iff (NumberField.Units.pos_at_place u w)).1 (hu w hw)
  have hge : 1 ≤ InfinitePlace.mk τ ((u : 𝓞 E) : E) :=
    InfinitePlace.one_le_of_lt_one (a := (u : 𝓞 E)) u.ne_zero (fun z hz => hlt z hz)
  have htr : ∀ n : ℕ, 0 ≤ ∑ φ : E →+* ℂ, (φ s).re * (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n := by
    intro n
    have h1 := h ((u : 𝓞 E) ^ n)
    have h2 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E)
      (x := s * (((u : 𝓞 E) ^ n : 𝓞 E) : E) * cc (((u : 𝓞 E) ^ n : 𝓞 E) : E))
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ)
      (fun φ : E →+* ℂ => φ (s * (((u : 𝓞 E) ^ n : 𝓞 E) : E) * cc (((u : 𝓞 E) ^ n : 𝓞 E) : E))) _
      (fun _ => rfl)] at h2
    have h3 := congrArg Complex.re h2
    rw [Complex.re_sum] at h3
    have h4 : (0 : ℝ) ≤ (algebraMap ℚ ℂ (Algebra.trace ℚ E
      (s * (((u : 𝓞 E) ^ n : 𝓞 E) : E) * cc (((u : 𝓞 E) ^ n : 𝓞 E) : E)))).re := by
      rw [eq_ratCast, Complex.ratCast_re]; exact_mod_cast h1
    rw [h3] at h4
    refine h4.trans_eq (Finset.sum_congr rfl fun φ _ => ?_)
    rw [map_mul, map_mul, map_cc, mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq,
      InfinitePlace.apply]
    push_cast
    rw [map_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
  let g : (E →+* ℂ) → ℕ → ℝ := fun φ n => if InfinitePlace.mk φ = InfinitePlace.mk τ then
    (if φ = τ then (τ s).re else |(φ s).re| * 0) else (φ s).re * (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n
  have hle : ∀ n φ, (φ s).re * (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n ≤ g φ n := by
    intro n φ
    simp only [g]
    split_ifs with h1 h2
    · subst h2
      have : 1 ≤ (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n := one_le_pow₀ (one_le_pow₀ hge)
      nlinarith
    · have hre : (φ s).re = (τ s).re := by
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · rw [h]
        · rw [← h]; simp
      rw [hre, mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
    · exact le_rfl
  have hlim : Filter.Tendsto (fun n => ∑ φ, g φ n) Filter.atTop
      (nhds (∑ φ : E →+* ℂ, if φ = τ then (τ s).re else 0)) := by
    refine tendsto_finset_sum _ fun φ _ => ?_
    simp only [g]
    by_cases h1 : InfinitePlace.mk φ = InfinitePlace.mk τ
    · simp only [if_pos h1, mul_zero]; exact tendsto_const_nhds
    · have h2 : φ ≠ τ := fun h => h1 (by rw [h])
      simp only [if_neg h1, if_neg h2]
      have h3 := hlt _ h1
      have h4 := apply_nonneg (InfinitePlace.mk φ) ((u : 𝓞 E) : E)
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2)
        (by positivity) (by nlinarith)).const_mul (φ s).re
      simpa using this
  have := ge_of_tendsto' hlim fun n => (htr n).trans (Finset.sum_le_sum fun φ _ => hle n φ)
  simp at this
  linarith

omit [IsCMField E] in

lemma cross_eq {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Finite ℤ Y]
    (hY : Module.finrank (𝓞 E) Y = 1) (η η' : Module.Dual ℤ Y) (x x' : Y) :
    pairE (E := E) η x * pairE η' x' = pairE η x' * pairE η' x := by
  haveI : Module.Finite (𝓞 E) Y := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hni : ¬ LinearIndependent (𝓞 E) ![x, x'] := fun h => by
    have := h.fintype_card_le_finrank
    rw [hY] at this
    simp at this
  rw [LinearIndependent.pair_iff] at hni
  push Not at hni
  obtain ⟨a, b, hab, hne⟩ := hni
  have key : ∀ θ : Module.Dual ℤ Y, (a : E) * pairE θ x + (b : E) * pairE θ x' = 0 := fun θ => by
    obtain ⟨h1, h2, -⟩ := pairE_properties E Y θ
    have h0 : pairE (E := E) θ (0 : Y) = 0 := by simpa using h1 0 0
    rw [← h1, ← h1, ← h2, hab, h0]
  have k1 := key η
  have k2 := key η'
  by_cases ha : a = 0
  · have hb : (b : E) ≠ 0 := by simpa using hne ha
    have ha' : (a : E) = 0 := by simp [ha]
    apply mul_left_cancel₀ hb
    rw [ha'] at k1 k2
    linear_combination (pairE η x) * k2 - (pairE η' x) * k1
  · have ha' : (a : E) ≠ 0 := by simpa using ha
    apply mul_left_cancel₀ ha'
    linear_combination (pairE η' x') * k1 - (pairE η x') * k2

variable {r : ℕ} (X : Data E r)

lemma eq_zero_of_herm_lattice (w : Fin r → E) (h : ∀ v ∈ X.Λ, herm X.Gm w v = 0) : w = 0 := by
  refine eq_zero_of_herm X.Gm X.Gm_det w fun y => ?_
  obtain ⟨d, hd, hy⟩ := exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := y) (by rw [X.Λ_span]; trivial)
  have h1 := h _ hy
  rw [show d • y = (d : E) • y from rfl, herm_smul_right] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (by simpa using h2) hd
  · exact h2

lemma eq_zero_of_trace_lattice (w : Fin r → E)
    (h : ∀ v ∈ X.Λ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm w v) = 0) : w = 0 := by
  refine eq_zero_of_herm_lattice X w fun v hv => ?_
  have := eq_zero_of_trace (X.ξ0 * herm X.Gm w v) fun β => by
    have h1 := h _ (X.Λ.smul_mem β hv)
    rw [show β • v = (β : E) • v from rfl, herm_smul_right] at h1
    rw [← h1]; congr 1; ring
  exact (mul_eq_zero.1 this).resolve_left X.ξ0_ne

lemma transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ v : Fin r → E) (α : E) :
    (transvMat G ξ α).mulVec v - v = (α * herm G v ξ) • ξ := by
  funext a
  simp only [transvMat, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    herm, add_sub_cancel_left, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

section Lattice

variable {La Y : Type} [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Y] [Module (𝓞 E) Y]
  (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
  (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
  (y : La →ₗ[𝓞 E] Y)

include iso in
lemma pairE_eq (t : La) (η : Module.Dual ℤ Y) (ht : ∀ v, -EF t v = η (y v)) (v : La) :
    pairE η (y v) = -X.ξ0 * herm X.Gm (φ v : Fin r → E) (φ t) := by
  obtain ⟨h1, -, h3, -⟩ := pairE_properties E Y η
  rw [← sub_eq_zero]
  refine eq_zero_of_trace_mul _ fun β => ?_
  rw [mul_sub, map_sub, ← h1, h3, ← map_smul, ← ht, Int.cast_neg, iso, ← trace_cc, cc_mul, cc_neg, X.ξ0_im,
    herm_conj _ X.Gm_herm, map_smul, show ((β • φ v : X.Λ) : Fin r → E) = (β : E) • (φ v : Fin r → E) from rfl,
    herm_smul_left, ← map_neg, ← map_sub, ← map_zero (Algebra.trace ℚ E)]
  congr 1; ring

include iso in

theorem rank_one [Module.Finite ℤ Y] (hY : Module.finrank (𝓞 E) Y = 1) (hκ : X.κ0 = 2 * X.ξ0)
    (hy : Function.Surjective y) (be : LinearMap.BilinForm ℤ Y) (hsym : ∀ a b, be a b = be b a)
    (hpos : ∀ a, a ≠ 0 → 0 < be a a) (nn : La →ₗ[𝓞 E] La) (hnn : ∀ v v', -EF (nn v) v' = be (y v) (y v'))
    (hrep : ∀ η : Module.Dual ℤ Y, ∃ t, ∀ v, -EF t v = η (y v))
    (ξ : Module.Dual ℤ Y) (hξ : ξ ≠ 0) (t : La) (ht : ∀ v, -EF t v = ξ (y v)) (hyt : y t = 0) :
    ∃ sE : E, X.IsIso (φ t : Fin r → E) ∧ IsBePar ξ be sE ∧ (∀ τ : E →+* ℂ, 0 < (τ sE).re) ∧
      (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
        (transvMat X.Gm (φ t : Fin r → E) (s * X.κ0)).mulVec v - v = (N : E) • u) ∧
      ∀ v, (φ (nn v) : Fin r → E) =
        (-(sE * X.κ0 * herm X.Gm (φ v : Fin r → E) (φ t))) • (φ t : Fin r → E) := by
  obtain ⟨p1, p2, p3, -⟩ := pairE_properties E Y ξ
  have hp := pairE_eq X φ EF iso y t ξ ht
  have hpn : ∀ v v', pairE (be (y v)) (y v') = -X.ξ0 * herm X.Gm (φ v' : Fin r → E) (φ (nn v)) :=
    fun v => pairE_eq X φ EF iso y (nn v) (be (y v)) (hnn v)
  have hξ0 := X.ξ0_ne
  have hc0 := X.ξ0_im
  have hcj := herm_conj X.Gm X.Gm_herm
  have hΛ : ∀ w ∈ X.Λ, ∃ v, (φ v : Fin r → E) = w := fun w hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩
  have hsm : ∀ (β : 𝓞 E) v, (φ (β • v) : Fin r → E) = (β : E) • (φ v : Fin r → E) := fun β v => by
    rw [map_smul]; rfl
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, ξ (y v₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (LinearMap.ext fun x => by obtain ⟨v, rfl⟩ := hy x; exact h v)
  have hp₀ : pairE (E := E) ξ (y v₀) ≠ 0 := fun h => by
    have := p3 (y v₀)
    rw [h, map_zero] at this
    exact hv₀ (by exact_mod_cast this.symm)
  set ξ' : Fin r → E := (φ t).1 with hξ'
  have hh₀ : herm X.Gm (φ v₀ : Fin r → E) ξ' ≠ 0 := fun h => hp₀ (by rw [hp, h, mul_zero])
  have hh₀' : herm X.Gm ξ' (φ v₀ : Fin r → E) ≠ 0 := by rw [← hcj]; simpa using hh₀
  have hskew : ∀ v v', herm X.Gm (φ (nn v) : Fin r → E) (φ v') = -herm X.Gm (φ v : Fin r → E) (φ (nn v')) := by
    intro v v'
    have : X.ξ0 * (herm X.Gm (φ (nn v) : Fin r → E) (φ v') + herm X.Gm (φ v : Fin r → E) (φ (nn v'))) = 0 := by
      refine eq_zero_of_trace_mul _ fun β => ?_
      have e1 : ((EF (nn (β • v)) v' : ℤ) : ℚ) = EF (nn v') (β • v) := by
        have := (hnn (β • v) v').trans ((hsym _ _).trans (hnn v' (β • v)).symm)
        exact_mod_cast neg_injective this
      rw [iso, iso, ← trace_cc (-X.ξ0 * herm X.Gm (φ (nn v') : Fin r → E) _), cc_mul, cc_neg, hc0, hcj,
        map_smul nn, hsm, hsm, herm_smul_left, herm_smul_left, ← sub_eq_zero, ← map_sub] at e1
      rw [← neg_eq_zero, ← map_neg, ← e1]
      congr 1; ring
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 this).resolve_left hξ0)
  have hmul : ∀ v, (φ (nn v) : Fin r → E) =
      (herm X.Gm (φ (nn v) : Fin r → E) (φ v₀) / herm X.Gm ξ' (φ v₀)) • ξ' := by
    intro v
    rw [← sub_eq_zero]
    refine eq_zero_of_herm_lattice X _ fun w hw => ?_
    obtain ⟨v', rfl⟩ := hΛ w hw
    have e := cross_eq (E := E) hY (be (y v)) ξ (y v') (y v₀)
    rw [hpn, hpn, hp, hp] at e
    have e' := congrArg cc e
    simp only [cc_mul, cc_neg, hc0, hcj, neg_neg] at e'
    rw [herm_sub_left, herm_smul_left]
    field_simp
    apply mul_left_cancel₀ (mul_ne_zero hξ0 hξ0)
    linear_combination e'
  obtain ⟨α, hα⟩ : ∃ α : E, ∀ v, (φ (nn v) : Fin r → E) = (α * herm X.Gm (φ v : Fin r → E) ξ') • ξ' := by
    refine ⟨-cc (herm X.Gm (φ (nn v₀) : Fin r → E) (φ v₀) / herm X.Gm ξ' (φ v₀)) / herm X.Gm ξ' (φ v₀),
      fun v => ?_⟩
    rw [hmul v, hskew v v₀]
    conv_lhs => rw [hmul v₀, herm_smul_right]
    congr 1; ring
  have hαc : cc α = -α := by
    have e := hskew v₀ v₀
    rw [hα, herm_smul_left, herm_smul_right, cc_mul, hcj] at e
    apply mul_left_cancel₀ (mul_ne_zero hh₀ hh₀')
    linear_combination e
  have hκ0 : X.κ0 ≠ 0 := by rw [hκ]; exact mul_ne_zero two_ne_zero hξ0
  have hcc2 : cc (2 : E) = 2 := by exact_mod_cast cc_natCast (E := E) 2
  have hsc : cc (-α / X.κ0) = -α / X.κ0 := by
    rw [div_eq_mul_inv, cc_mul, cc_neg, hαc, cc_inv, hκ, cc_mul, hcc2, hc0]
    field_simp
  have htr : ∀ (s : E) v v', Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ (y v'))) =
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm ((s * X.κ0 * herm X.Gm (φ v : Fin r → E) ξ') • ξ') (φ v')) := by
    intro s v v'
    rw [hp, hp, cc_mul, cc_neg, hc0, hcj, herm_smul_left, hκ]
    congr 1; ring
  have hbe : IsBePar ξ be (-α / X.κ0) := by
    refine ⟨hsc, fun x x' => ?_⟩
    obtain ⟨v, rfl⟩ := hy x
    obtain ⟨v', rfl⟩ := hy x'
    rw [htr, ← hnn, Int.cast_neg, iso, hα v, ← map_neg, herm_smul_left, herm_smul_left]
    congr 1; field_simp
  refine ⟨-α / X.κ0, ⟨(φ t).2, ?_, fun h => hh₀ ?_⟩, hbe, fun τ => ?_, fun N s hs w hw => ?_, fun v => ?_⟩
  · have e := hp t
    have h0 : pairE (E := E) ξ (0 : Y) = 0 := by simpa using p1 0 0
    rw [hyt, h0] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (neg_ne_zero.2 hξ0)
  · rw [h]; simp [herm]
  · set sE := -α / X.κ0
    have hs0 : sE ≠ 0 := fun h => by
      have e := hbe.2 (y v₀) (y v₀)
      have := hpos (y v₀) fun h => hv₀ (by rw [h, map_zero])
      rw [h] at e
      simp only [mul_zero, zero_mul, map_zero] at e
      have e' : be (y v₀) (y v₀) = 0 := by exact_mod_cast e.symm
      omega
    have h1 := re_nonneg_of_trace (2 * sE * pairE ξ (y v₀) * cc (pairE ξ (y v₀))) (fun a => by
      have e := hbe.2 (a • y v₀) (a • y v₀)
      rw [p1, cc_mul] at e
      have h2 : (0 : ℤ) ≤ be (a • y v₀) (a • y v₀) := by
        by_cases h : a • y v₀ = 0
        · simp [h]
        · exact (hpos _ h).le
      have h3 : (0 : ℚ) ≤ (be (a • y v₀) (a • y v₀) : ℤ) := by exact_mod_cast h2
      rw [← e] at h3
      refine h3.trans_eq ?_
      congr 1; ring) τ
    have him : (τ sE).im = 0 := by
      have := map_cc τ sE
      rw [hsc] at this
      exact Complex.conj_eq_iff_im.1 this.symm
    have hre : (τ sE).re ≠ 0 := fun h => hs0 (τ.injective (by rw [map_zero]; exact Complex.ext h him))
    have hn : 0 < Complex.normSq (τ (pairE ξ (y v₀))) := Complex.normSq_pos.2 ((map_ne_zero τ).2 hp₀)
    rw [map_mul, map_mul, map_mul, map_cc, mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, map_ofNat] at h1
    have h4 : ((2 : ℂ) * τ sE).re = 2 * (τ sE).re := by simp
    rw [h4] at h1
    have : 0 ≤ (τ sE).re := by
      by_contra hh
      push Not at hh
      nlinarith
    exact lt_of_le_of_ne this hre.symm
  · obtain ⟨v, rfl⟩ := hΛ w hw
    obtain ⟨η, hη⟩ : ∃ η : Module.Dual ℤ Y, ∀ x,
        Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ x)) = (N : ℚ) * η x := by
      by_cases hN : N = 0
      · refine ⟨0, fun x => ?_⟩
        obtain ⟨m, hm⟩ := hs.2 (y v) x
        rw [hm, hN]; simp
      · choose m hm using hs.2 (y v)
        have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
        refine ⟨(AddMonoidHom.mk' m fun a b => ?_).toIntLinearMap, hm⟩
        have e := hm (a + b)
        rw [p2, cc_add, mul_add, map_add, hm, hm, ← mul_add] at e
        exact_mod_cast (mul_left_cancel₀ hN' e).symm
    obtain ⟨t', ht'⟩ := hrep η
    refine ⟨-(φ t' : Fin r → E), X.Λ.neg_mem (φ t').2, ?_⟩
    rw [transvMat_mulVec, ← sub_eq_zero]
    refine eq_zero_of_trace_lattice X _ fun w hw => ?_
    obtain ⟨v', rfl⟩ := hΛ w hw
    have e := hη (y v')
    rw [htr, ← ht', Int.cast_neg, iso, ← map_neg, ← nsmul_eq_mul, ← map_nsmul, ← sub_eq_zero, ← map_sub] at e
    rw [← neg_eq_zero, ← map_neg, ← e, herm_sub_left, smul_neg, ← neg_smul, herm_smul_left X.Gm (-(N : E))]
    congr 1; rw [nsmul_eq_mul]; ring
  · rw [hα v]
    congr 1; field_simp

end Lattice

end GlobalTheory.ArcFlow
