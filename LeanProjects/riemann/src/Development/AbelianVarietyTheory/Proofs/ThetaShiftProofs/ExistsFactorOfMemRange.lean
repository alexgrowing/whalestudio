import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

theorem tsum_mem_range_of_norm_cut (T : CDVR) {K : Type} [NormedField K] [CompleteSpace K] (i' : T.Fr →+* K)
    (hn : ∀ x : T.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V T.Fr)) (t : T.V)
    (ht : ‖i' (algebraMap T.V T.Fr t)‖ < 1) (a : ℕ → T.V) :
    ∃ L : T.V, i' (algebraMap T.V T.Fr L) =
      ∑' k : ℕ, i' (algebraMap T.V T.Fr (a k)) * i' (algebraMap T.V T.Fr t) ^ k := by
  set φ : T.V →+* K := i'.comp (algebraMap T.V T.Fr) with hφ
  have hle : ∀ v : T.V, ‖φ v‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  change ‖φ t‖ < 1 at ht
  change ∃ L : T.V, φ L = ∑' k : ℕ, φ (a k) * φ t ^ k
  have htm : t ∈ IsLocalRing.maximalIdeal T.V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h1 : ‖φ u‖ * ‖φ (u⁻¹ : T.Vˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul]; simp
    have h2 := hle (u⁻¹ : T.Vˣ)
    nlinarith [norm_nonneg (φ u), norm_nonneg (φ (u⁻¹ : T.Vˣ))]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hπn : ‖φ π‖ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖i' (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv⟩ := (hn _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv, map_one, mul_inv_cancel₀ hπ0]
  have hpow : ∀ (n : ℕ) (x : T.V), x ∈ IsLocalRing.maximalIdeal T.V ^ n → ‖φ x‖ ≤ ‖φ π‖ ^ n := by
    intro n x hx
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨b, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle b)
  let S : ℕ → T.V := fun n => ∑ k ∈ Finset.range n, a k * t ^ k
  have hS : ∀ {m n : ℕ}, m ≤ n →
      S m ≡ S n [SMOD (IsLocalRing.maximalIdeal T.V ^ m • ⊤ : Submodule T.V T.V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    simp only [S]
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (Ideal.pow_mem_pow htm k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal T.V) (M := T.V) inferInstance hS
  refine ⟨L, ?_⟩
  have hsum : Summable fun k : ℕ => φ (a k) * φ t ^ k := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) ht) fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle _)
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, φ (a k) * φ t ^ k) Filter.atTop (nhds (φ L)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπn)
    have h3 := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h3
    have h4 := hpow n _ h3
    simpa [S, map_sub, map_sum] using h4
  exact tendsto_nhds_unique h2 h1

theorem exists_factor_of_mem_range {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C) (g : B →+* C)
    (hg : Function.Injective g) (h : ∀ a, ∃ b, g b = f a) : ∃ e : A →+* B, g.comp e = f := by
  choose e he using h
  refine ⟨{ toFun := e, map_one' := hg ?_, map_mul' := fun x y => hg ?_, map_zero' := hg ?_,
            map_add' := fun x y => hg ?_ }, RingHom.ext he⟩ <;> simp [he]

theorem eval_factors_through_cdvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv T' : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K) (j : Tv.V →+* T'.V) (i' : T'.Fr →+* K), ϖ ≠ 0 → (∀ v, i' (algebraMap T'.V T'.Fr (j v)) = ιT (algebraMap Tv.V Tv.Fr v)) → (∀ x : T'.Fr, ‖i' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V T'.Fr)) → ∀ (t : T'.V) (Y : ArcLt Dw → T'.V) (ev : ArcSR Dw Tv.V ϖ →+* K), ‖i' (algebraMap T'.V T'.Fr t)‖ < 1 → (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * i' (algebraMap T'.V T'.Fr t) ^ k) → (∀ x, ev (arcXR Dw Tv.V ϖ x) = i' (algebraMap T'.V T'.Fr (Y x))) → ∃ (e₀ : PowerSeries Tv.V →+* T'.V) (e₁ : ArcSR Dw Tv.V ϖ →+* T'.Fr), e₀.comp (PowerSeries.C (R := Tv.V)) = j ∧ e₁.comp (arcιR Dw Tv.V ϖ) = (algebraMap T'.V T'.Fr).comp e₀ ∧ (∀ x, e₁ (arcXR Dw Tv.V ϖ x) = algebraMap T'.V T'.Fr (Y x)) ∧ i'.comp e₁ = ev := by
  intro E _ _ _ H Dw Tv T' ϖ K _ _ _ ιT j i' _ hj hn t Y ev ht hp hX
  have hinj : Function.Injective (i'.comp (algebraMap T'.V T'.Fr)) :=
    i'.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have h0 : ∀ p : PowerSeries Tv.V,
      ∃ b, (i'.comp (algebraMap T'.V T'.Fr)) b = (ev.comp (arcιR Dw Tv.V ϖ)) p := by
    intro p
    obtain ⟨L, hL⟩ := tsum_mem_range_of_norm_cut T' i' hn t ht (fun k => j (PowerSeries.coeff k p))
    refine ⟨L, ?_⟩
    simp only [RingHom.comp_apply]
    rw [hL, hp]
    simp only [hj]
  obtain ⟨e₀, he₀⟩ := exists_factor_of_mem_range _ _ hinj h0
  have hpoly : ∀ a : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V),
      ev (algebraMap _ (ArcSR Dw Tv.V ϖ) a) ∈ i'.fieldRange := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C p =>
      obtain ⟨b, hb⟩ := h0 p
      exact ⟨_, hb⟩
    | add p q hp' hq' => rw [map_add, map_add]; exact add_mem hp' hq'
    | mul_X p x hp' =>
      rw [map_mul (algebraMap _ (ArcSR Dw Tv.V ϖ)) p, map_mul ev]
      exact mul_mem hp' ⟨_, (hX x).symm⟩
  have h1 : ∀ z : ArcSR Dw Tv.V ϖ, ∃ b, i' b = ev z := by
    intro z
    obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj
      (Submonoid.powers (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) z
    have hu := (IsLocalization.map_units (ArcSR Dw Tv.V ϖ) s).map ev
    have hz' := congrArg ev hz
    rw [map_mul ev] at hz'
    have : ev z ∈ i'.fieldRange := by
      rw [eq_div_of_mul_eq hu.ne_zero hz']
      exact div_mem (hpoly _) (hpoly _)
    exact this
  obtain ⟨e₁, he₁⟩ := exists_factor_of_mem_range _ _ i'.injective h1
  refine ⟨e₀, e₁, ?_, ?_, fun x => ?_, he₁⟩
  · refine RingHom.ext fun v => hinj ?_
    have h2 := RingHom.congr_fun he₀ (PowerSeries.C v)
    simp only [RingHom.comp_apply] at h2 ⊢
    rw [h2, hp, tsum_eq_single 0, hj]
    · simp
    · intro k hk
      simp [PowerSeries.coeff_C, hk]
  · refine RingHom.ext fun p => i'.injective ?_
    have h2 := RingHom.congr_fun he₀ p
    have h3 := RingHom.congr_fun he₁ (arcιR Dw Tv.V ϖ p)
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [h2, h3]
  · apply i'.injective
    rw [← hX x]
    exact RingHom.congr_fun he₁ _

end GlobalTheory.ArcQ
