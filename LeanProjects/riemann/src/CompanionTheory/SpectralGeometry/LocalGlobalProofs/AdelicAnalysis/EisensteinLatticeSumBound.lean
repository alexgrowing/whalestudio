import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.LatSum

theorem hasSum_tele {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) (1 / y) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1) := by
    intro n
    have h0 : 0 < (n : ℝ) + y := by positivity
    have : 1 / ((n : ℝ) + y + 1) ≤ 1 / ((n : ℝ) + y) :=
      one_div_le_one_div_of_le h0 (by linarith)
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + y) - 1 / ((i : ℝ) + y + 1))
      = 1 / y - 1 / ((n : ℝ) + y) := by
    intro n
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + y)) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ring
  simp_rw [hpart]
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + y)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ y tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub h0

theorem pt_bound {t u y : ℝ} (ht : 0 < t) (hy : t ≤ y) (hu : y ≤ u) (m : ℕ) :
    (u ^ (m + 2))⁻¹ ≤ (1 + 1 / t) * (y ^ m)⁻¹ * (1 / u - 1 / (u + 1)) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : 1 / u - 1 / (u + 1) = (u * (u + 1))⁻¹ := by
    field_simp
    ring
  have h2 : (u ^ 2)⁻¹ ≤ (1 + 1 / t) * (u * (u + 1))⁻¹ := by
    have h5 : 1 / u ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith)
    have h3 : (u ^ 2)⁻¹ = (1 + 1 / u) * (u * (u + 1))⁻¹ := by
      field_simp
    rw [h3]
    have : 0 ≤ (u * (u + 1))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) this
  have h4 : (u ^ m)⁻¹ ≤ (y ^ m)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ hy0.le hu m
  calc (u ^ (m + 2))⁻¹ = (u ^ m)⁻¹ * (u ^ 2)⁻¹ := by rw [pow_add, mul_inv]
    _ ≤ (y ^ m)⁻¹ * ((1 + 1 / t) * (u * (u + 1))⁻¹) :=
        mul_le_mul h4 h2 (by positivity) (by positivity)
    _ = (1 + 1 / t) * (y ^ m)⁻¹ * (1 / u - 1 / (u + 1)) := by rw [h1]; ring

theorem sum_int {t y : ℝ} (ht : 0 < t) (hy : t ≤ y) (m : ℕ) :
    Summable (fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) ∧
      ∑' k : ℤ, ((|(k : ℝ)| + y) ^ (m + 2))⁻¹ ≤ 2 * (1 + 1 / t) * (y * (y ^ (m + 2))⁻¹) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨B, hB⟩ : ∃ B, B = (1 + 1 / t) * (y ^ m)⁻¹ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hs : HasSum (fun n : ℕ => B * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1))) (B * (1 / y)) :=
    (hasSum_tele hy0).mul_left B
  have nn : ∀ k : ℤ, 0 ≤ ((|(k : ℝ)| + y) ^ (m + 2))⁻¹ := fun k => by positivity
  have hp : ∀ n : ℕ, ((|(((n : ℤ)) : ℝ)| + y) ^ (m + 2))⁻¹
      ≤ B * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) := by
    intro n
    have e : |(((n : ℤ)) : ℝ)| = (n : ℝ) := by simp
    rw [e, hB]
    exact pt_bound ht hy (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) m
  have hn : ∀ n : ℕ, ((|((-((n : ℤ) + 1) : ℤ) : ℝ)| + y) ^ (m + 2))⁻¹
      ≤ B * (1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) := by
    intro n
    refine le_trans ?_ (hp n)
    have e : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have e' : |(((n : ℤ)) : ℝ)| = (n : ℝ) := by simp
    rw [e, e']
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have s1 : Summable (fun n : ℕ => ((|(((n : ℤ)) : ℝ)| + y) ^ (m + 2))⁻¹) :=
    Summable.of_nonneg_of_le (fun n => nn n) hp hs.summable
  have s2 : Summable (fun n : ℕ => ((|((-((n : ℤ) + 1) : ℤ) : ℝ)| + y) ^ (m + 2))⁻¹) :=
    Summable.of_nonneg_of_le (fun n => nn _) hn hs.summable
  refine ⟨Summable.of_nat_of_neg_add_one (f := fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) s1 s2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) s1 s2]
  have e1 := s1.tsum_le_tsum hp hs.summable
  have e2 := s2.tsum_le_tsum hn hs.summable
  rw [hs.tsum_eq] at e1 e2
  have e3 : B * (1 / y) = (1 + 1 / t) * (y * (y ^ (m + 2))⁻¹) := by
    rw [hB]
    field_simp
    ring
  rw [e3] at e1 e2
  linarith

theorem norm_lower {t : ℝ} (ht : 0 < t) (z : ℂ) (hz : t ≤ z.im) (s : ℝ) :
    (2 + 1 / t)⁻¹ * (|((⌊z.re + s⌋ : ℤ) : ℝ)| + z.im) ≤ ‖z + (s : ℂ)‖ := by
  have hc : 0 < 2 + 1 / t := by positivity
  rw [inv_mul_le_iff₀ hc]
  obtain ⟨v, hv⟩ : ∃ v, v = z + (s : ℂ) := ⟨_, rfl⟩
  rw [← hv]
  have hre : v.re = z.re + s := by rw [hv]; simp
  have him : v.im = z.im := by rw [hv]; simp
  have h1 : |v.re| ≤ ‖v‖ := Complex.abs_re_le_norm v
  have h2 : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
  have h3 : z.im ≤ ‖v‖ := by rw [← him]; exact (le_abs_self _).trans h2
  rw [← hre]
  have h4 : |((⌊v.re⌋ : ℤ) : ℝ)| ≤ |v.re| + 1 := by
    have a1 := Int.floor_le v.re
    have a2 := Int.lt_floor_add_one v.re
    rw [abs_le]
    constructor
    · have := neg_abs_le v.re
      linarith
    · have := le_abs_self v.re
      linarith
  have h5 : 1 ≤ ‖v‖ * (1 / t) := by
    have : t ≤ ‖v‖ := hz.trans h3
    rw [mul_one_div, le_div_iff₀ ht]
    linarith
  nlinarith

theorem finite_small (F : Type) [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    {α : 𝓞 F | ∀ w, |ρ w (α : F)| < 1}.Finite := by
  have hf := Embeddings.finite_of_norm_le F ℂ 1
  refine (hf.preimage (f := fun α : 𝓞 F => (α : F)) ?_).subset ?_
  · exact (RingOfIntegers.coe_injective).injOn
  · intro α hα
    refine ⟨RingOfIntegers.isIntegral_coe α, fun φ => ?_⟩
    have h1 : ‖φ (α : F)‖ = InfinitePlace.mk φ (α : F) := (InfinitePlace.apply φ _).symm
    have h2 := InfinitePlace.norm_embedding_eq (InfinitePlace.mk φ) (α : F)
    rw [h1, ← h2, ← hρ, Complex.norm_real, Real.norm_eq_abs]
    exact (hα _).le

open Classical in

theorem sum_le_of_fibres {α ι : Type} [Fintype ι] (a : α → ℝ) (φ : α → ι → ℤ)
    (g : ι → ℤ → ℝ) (K : ℕ) (ha : ∀ r, 0 ≤ a r) (hg : ∀ w k, 0 ≤ g w k)
    (hgs : ∀ w, Summable (g w)) (hle : ∀ r, a r ≤ ∏ w, g w (φ r w))
    (hfib : ∀ (T : Finset α) (n : ι → ℤ), (T.filter fun r => φ r = n).card ≤ K) :
    Summable a ∧ ∑' r, a r ≤ K * ∏ w, ∑' k, g w k := by
  have key : ∀ T : Finset α, ∑ r ∈ T, a r ≤ K * ∏ w, ∑' k, g w k := by
    intro T
    have hG : ∀ n : ι → ℤ, 0 ≤ ∏ w, g w (n w) :=
      fun n => Finset.prod_nonneg fun w _ => hg w _
    have s1 : ∑ r ∈ T, a r ≤ ∑ r ∈ T, ∏ w, g w (φ r w) := Finset.sum_le_sum fun r _ => hle r
    have s2 : ∑ r ∈ T, ∏ w, g w (φ r w)
        = ∑ n ∈ T.image φ, (T.filter fun r => φ r = n).card • ∏ w, g w (n w) :=
      Finset.sum_comp (fun n : ι → ℤ => ∏ w, g w (n w)) φ
    have s3 : ∑ n ∈ T.image φ, (T.filter fun r => φ r = n).card • ∏ w, g w (n w)
        ≤ ∑ n ∈ T.image φ, (K : ℝ) * ∏ w, g w (n w) := by
      refine Finset.sum_le_sum fun n _ => ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib T n) (hG n)
    have s4 : ∑ n ∈ T.image φ, ∏ w, g w (n w)
        ≤ ∑ n ∈ Fintype.piFinset (fun w => (T.image φ).image (fun n => n w)), ∏ w, g w (n w) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hG n
      intro n hn
      rw [Fintype.mem_piFinset]
      intro w
      exact Finset.mem_image_of_mem _ hn
    have s5 : ∑ n ∈ Fintype.piFinset (fun w => (T.image φ).image (fun n => n w)), ∏ w, g w (n w)
        ≤ ∏ w, ∑' k, g w k := by
      rw [← Finset.prod_univ_sum]
      refine Finset.prod_le_prod (fun w _ => Finset.sum_nonneg fun k _ => hg w k) fun w _ => ?_
      exact (hgs w).sum_le_tsum _ fun k _ => hg w k
    rw [← Finset.mul_sum] at s3
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc ∑ r ∈ T, a r ≤ _ := s1
      _ = _ := s2
      _ ≤ _ := s3
      _ ≤ _ := mul_le_mul_of_nonneg_left (s4.trans s5) hK
  have hsum : Summable a := summable_of_sum_le ha key
  exact ⟨hsum, hsum.tsum_le_of_sum_le key⟩

open Classical in

theorem fibre_card (F : Type) [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (S : Finset (𝓞 F)) (hS : ∀ α : 𝓞 F, (∀ w, |ρ w (α : F)| < 1) → α ∈ S)
    (x : InfinitePlace F → ℝ) (T : Finset (𝓞 F)) (n : InfinitePlace F → ℤ) :
    (T.filter fun r : 𝓞 F => (fun w => ⌊x w + ρ w (r : F)⌋) = n).card ≤ S.card := by
  rcases (T.filter fun r : 𝓞 F => (fun w => ⌊x w + ρ w (r : F)⌋) = n).eq_empty_or_nonempty with h | ⟨r₀, h₀⟩
  · rw [h]
    simp
  · refine Finset.card_le_card_of_injOn (fun r => r - r₀) ?_ ?_
    · intro r hr
      apply hS
      intro w
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hr)).2
      have e0 := (Finset.mem_filter.1 h₀).2
      have e : ⌊x w + ρ w (r : F)⌋ = ⌊x w + ρ w (r₀ : F)⌋ := by
        rw [congrFun e1 w, congrFun e0 w]
      have := Int.abs_sub_lt_one_of_floor_eq_floor e
      have e2 : ρ w ((r - r₀ : 𝓞 F) : F) = (x w + ρ w (r : F)) - (x w + ρ w (r₀ : F)) := by
        push_cast
        rw [map_sub]
        ring
      rw [e2]
      exact this
    · intro a _ b _ hab
      exact sub_left_injective hab

theorem lattice_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ M : ℕ, 2 ≤ M → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) →
      Summable (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) ∧
      ∑' r : 𝓞 F, (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ C * ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ := by
  intro F _ _ _ ρ hρ M hM t ht
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  have hfin := finite_small F ρ hρ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 + 1 / t)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨(hfin.toFinset.card : ℝ) * ((c ^ (m + 2))⁻¹ * (2 * (1 + 1 / t))) ^
    Fintype.card (InfinitePlace F), fun τ hτ => ?_⟩
  have hy0 : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (hτ w)
  have hint := fun w => sum_int ht (hτ w) m
  have hmain := sum_le_of_fibres
    (fun r : 𝓞 F => (∏ w, ‖τ w + (ρ w (r : F) : ℝ)‖ ^ (m + 2))⁻¹)
    (fun r w => ⌊(τ w).re + ρ w (r : F)⌋)
    (fun w k => (c ^ (m + 2))⁻¹ * ((|(k : ℝ)| + (τ w).im) ^ (m + 2))⁻¹)
    hfin.toFinset.card
    (fun r => by positivity)
    (fun w k => by have := hy0 w; positivity)
    (fun w => (hint w).1.mul_left _)
    (fun r => by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
      have h1 := norm_lower ht (τ w) (hτ w) (ρ w (r : F))
      rw [← hc] at h1
      have hpos : 0 < c * (|((⌊(τ w).re + ρ w (r : F)⌋ : ℤ) : ℝ)| + (τ w).im) := by
        have := hy0 w
        positivity
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le h1 _))
    (fun T n => by
      classical
      exact fibre_card F ρ hfin.toFinset (fun α hα => hfin.mem_toFinset.2 hα)
        (fun w => (τ w).re) T n)
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  have hK : (0 : ℝ) ≤ hfin.toFinset.card := Nat.cast_nonneg _
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK
  have hconst : ((c ^ (m + 2))⁻¹ * (2 * (1 + 1 / t))) ^ Fintype.card (InfinitePlace F)
      = ∏ _w : InfinitePlace F, ((c ^ (m + 2))⁻¹ * (2 * (1 + 1 / t))) := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [hconst, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => ?_) fun w _ => ?_
  · exact tsum_nonneg fun k => by have := hy0 w; positivity
  · rw [tsum_mul_left, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (hint w).2

end GlobalTheory.CompanionTheory.SW.LatSum
