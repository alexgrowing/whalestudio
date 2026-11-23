import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieEta
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.AlTieLG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.AlTie
  Formalism.L2.SG.Pf.AlTieEta Filter Topology

theorem newton_quad {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (tr nm c : K) (hc : tr ^ 2 - 4 * nm = c) (hc1 : ‖c‖ = 1) (h4 : ‖(4 : K)‖ ≤ 1)
    (a₀ : K) (h0 : ‖a₀ ^ 2 - tr * a₀ + nm‖ < 1) : ∃ α : K, α ^ 2 - tr * α + nm = 0 := by
  let f : K → K := fun a => a ^ 2 - tr * a + nm
  let f' : K → K := fun a => 2 * a - tr
  have hid : ∀ a, f' a ^ 2 = 4 * f a + c := by
    intro a; simp only [f, f']; rw [← hc]; ring
  have hder : ∀ a, ‖f a‖ < 1 → ‖f' a‖ = 1 := by
    intro a ha
    have h1 : ‖4 * f a‖ < 1 := by
      rw [norm_mul]
      calc ‖(4 : K)‖ * ‖f a‖ ≤ 1 * ‖f a‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact ha
    have h2 : ‖f' a ^ 2‖ = 1 := by
      rw [hid, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hc1]; exact h1.ne), hc1]
      exact max_eq_right h1.le
    rw [norm_pow] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  have hstep : ∀ a, f' a ≠ 0 → f (a - f a / f' a) = (f a / f' a) ^ 2 := by
    intro a ha
    have e : f a / f' a * f' a = f a := div_mul_cancel₀ _ ha
    have e2 : f (a - f a / f' a) = f a - f a / f' a * f' a + (f a / f' a) ^ 2 := by
      simp only [f, f']; ring
    rw [e2, e, sub_self, zero_add]
  let seq : ℕ → K := fun n => Nat.rec a₀ (fun _ a => a - f a / f' a) n
  have hseq : ∀ n, seq (n + 1) = seq n - f (seq n) / f' (seq n) := fun n => rfl
  have hρ0 : 0 ≤ ‖f a₀‖ := norm_nonneg _
  have hbound : ∀ n, ‖f (seq n)‖ ≤ ‖f a₀‖ ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp [seq]
    | succ n ih =>
      have hlt : ‖f (seq n)‖ < 1 := lt_of_le_of_lt ih (pow_lt_one₀ hρ0 h0 (by positivity))
      have hd := hder _ hlt
      have hne : f' (seq n) ≠ 0 := by
        intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
      rw [hseq, hstep _ hne, norm_pow, norm_div, hd, div_one]
      calc ‖f (seq n)‖ ^ 2 ≤ (‖f a₀‖ ^ 2 ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ih 2
        _ = ‖f a₀‖ ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ]
  have hbound' : ∀ n, ‖f (seq n)‖ ≤ ‖f a₀‖ ^ n := fun n =>
    (hbound n).trans (pow_le_pow_of_le_one hρ0 h0.le (Nat.lt_two_pow_self).le)
  have hdist : ∀ n, dist (seq n) (seq (n + 1)) ≤ 1 * ‖f a₀‖ ^ n := by
    intro n
    have hlt : ‖f (seq n)‖ < 1 := lt_of_le_of_lt (hbound n) (pow_lt_one₀ hρ0 h0 (by positivity))
    have hd := hder _ hlt
    rw [dist_eq_norm, hseq, sub_sub_cancel, norm_div, hd, div_one, one_mul]
    exact hbound' n
  have hcs : CauchySeq seq := cauchySeq_of_le_geometric _ _ h0 hdist
  obtain ⟨α, hα⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨α, ?_⟩
  have hcont : Continuous f := by simp only [f]; fun_prop
  have h1 : Tendsto (fun n => f (seq n)) atTop (𝓝 (f α)) := (hcont.tendsto α).comp hα
  have h2 : Tendsto (fun n => f (seq n)) atTop (𝓝 0) :=
    squeeze_zero_norm hbound' (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 h0)
  exact tendsto_nhds_unique h1 h2

section Quad

variable {K A : Type} [Field K] [CommRing A] [Algebra K A] (T : A) (t n : K)

structure QuadAlg : Prop where
  span : ∀ z : A, ∃ x y : K, z = x • (1 : A) + y • T
  indep : ∀ x y : K, x • (1 : A) + y • T = 0 → x = 0 ∧ y = 0
  rel : T * T = algebraMap K A t * T - algebraMap K A n
  disc : t ^ 2 - 4 * n ≠ 0

variable {T t n}

theorem QuadAlg.span' (hQ : QuadAlg T t n) (z : A) : ∃ x y : K, z = algebraMap K A x + algebraMap K A y * T := by
  obtain ⟨x, y, hz⟩ := hQ.span z
  exact ⟨x, y, by rw [hz, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

theorem QuadAlg.indep' (hQ : QuadAlg T t n) (x y : K) (h : algebraMap K A x + algebraMap K A y * T = 0) :
    x = 0 ∧ y = 0 := hQ.indep x y (by rw [Algebra.smul_def, Algebra.smul_def, mul_one]; exact h)

private theorem linear_mul_linear_of_quadAlg (hQ : QuadAlg T t n) (p q p' q' : K) :
    (algebraMap K A p * T + algebraMap K A q) * (algebraMap K A p' * T + algebraMap K A q') =
      algebraMap K A (p * q' + q * p' + p * p' * t) * T + algebraMap K A (q * q' - p * p' * n) := by
  simp only [map_add, map_sub, map_mul]
  linear_combination (algebraMap K A p * algebraMap K A p') * hQ.rel

theorem root_of_idem (hQ : QuadAlg T t n) (h : IdemNT A) : ∃ β : K, β ^ 2 - t * β + n = 0 := by
  obtain ⟨e, he, he0, he1⟩ := h
  obtain ⟨x, y, rfl⟩ := hQ.span' e
  have he' : (algebraMap K A y * T + algebraMap K A x) * (algebraMap K A y * T + algebraMap K A x) =
      algebraMap K A y * T + algebraMap K A x := by
    rw [add_comm (algebraMap K A y * T)]
    exact he
  rw [linear_mul_linear_of_quadAlg hQ] at he'
  have key : algebraMap K A (x * x - y * y * n - x) +
      algebraMap K A (y * x + x * y + y * y * t - y) * T = 0 := by
    simp only [map_sub, map_add, map_mul] at he' ⊢
    linear_combination he'
  obtain ⟨h1, h2⟩ := hQ.indep' _ _ key
  by_cases hy : y = 0
  · exfalso
    subst hy
    have hx : x * (x - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 hx with hx | hx
    · apply he0
      rw [hx]
      simp
    · apply he1
      rw [sub_eq_zero.1 hx]
      simp
  · have h2' : 2 * x + y * t - 1 = 0 := by
      have h3 : y * (2 * x + y * t - 1) = 0 := by linear_combination h2
      exact (mul_eq_zero.1 h3).resolve_left hy
    refine ⟨x / y + t, ?_⟩
    rw [show (x / y + t) ^ 2 - t * (x / y + t) + n = (x ^ 2 + x * y * t + n * y ^ 2) / y ^ 2 by
      field_simp
      ring]
    rw [div_eq_zero_iff]
    left
    linear_combination x * h2' - h1

theorem idem_of_root (hQ : QuadAlg T t n) {β : K} (hβ : β ^ 2 - t * β + n = 0) : IdemNT A := by
  have hd : (2 * β - t) ^ 2 ≠ 0 := by
    rw [show (2 * β - t) ^ 2 = t ^ 2 - 4 * n by linear_combination 4 * hβ]
    exact hQ.disc
  have hne : 2 * β - t ≠ 0 := fun h0 => hd (by rw [h0]; ring)
  set c := (2 * β - t)⁻¹ with hc_def
  have hc : c * (2 * β - t) = 1 := inv_mul_cancel₀ hne
  have hc0 : c ≠ 0 := inv_ne_zero hne
  refine ⟨algebraMap K A c * T + algebraMap K A (-(c * (t - β))), ?_, ?_, ?_⟩
  · rw [linear_mul_linear_of_quadAlg hQ]
    have hX : c * -(c * (t - β)) + -(c * (t - β)) * c + c * c * t = c := by
      linear_combination c * hc
    have hY : -(c * (t - β)) * -(c * (t - β)) - c * c * n = -(c * (t - β)) := by
      linear_combination (-c * (t - β)) * hc - c ^ 2 * hβ
    rw [hX, hY]
  · intro h0
    have h1 : algebraMap K A (-(c * (t - β))) + algebraMap K A c * T = 0 := by
      rw [add_comm]
      exact h0
    exact hc0 (hQ.indep' _ _ h1).2
  · intro h0
    have h1 : algebraMap K A (-(c * (t - β)) - 1) + algebraMap K A c * T = 0 := by
      rw [map_sub, map_one]
      linear_combination h0
    exact hc0 (hQ.indep' _ _ h1).2

theorem idem_iff_root (hQ : QuadAlg T t n) : IdemNT A ↔ ∃ β : K, β ^ 2 - t * β + n = 0 :=
  ⟨root_of_idem hQ, fun ⟨_, hβ⟩ => idem_of_root hQ hβ⟩

theorem unit_of_noRoot (hQ : QuadAlg T t n) (h : ¬ ∃ β : K, β ^ 2 - t * β + n = 0) :
    ∀ z : A, z ≠ 0 → IsUnit z := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := hQ.span' z
  set N := x ^ 2 + x * y * t + y ^ 2 * n with hN_def
  have hN : N ≠ 0 := by
    intro hN0
    by_cases hy : y = 0
    · apply hz
      have hx : x = 0 := by
        have : x ^ 2 = 0 := by rw [hN_def, hy] at hN0; linear_combination hN0
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      rw [hx, hy]
      simp
    · apply h
      refine ⟨-x / y, ?_⟩
      rw [show (-x / y) ^ 2 - t * (-x / y) + n = N / y ^ 2 by
        rw [hN_def]
        field_simp
        ring]
      rw [hN0, zero_div]
  have hw : (algebraMap K A x + algebraMap K A y * T) *
      (algebraMap K A (-(N⁻¹ * y)) * T + algebraMap K A (N⁻¹ * (x + y * t))) = 1 := by
    rw [add_comm (algebraMap K A x), linear_mul_linear_of_quadAlg hQ]
    have hX : y * (N⁻¹ * (x + y * t)) + x * -(N⁻¹ * y) + y * -(N⁻¹ * y) * t = 0 := by ring
    have hY : x * (N⁻¹ * (x + y * t)) - y * -(N⁻¹ * y) * n = 1 := by
      rw [show x * (N⁻¹ * (x + y * t)) - y * -(N⁻¹ * y) * n = N⁻¹ * N by rw [hN_def]; ring]
      exact inv_mul_cancel₀ hN
    rw [hX, hY, map_zero, map_one, zero_mul, zero_add]
  exact ⟨⟨_, _, hw, by rw [mul_comm]; exact hw⟩, rfl⟩

theorem field_iff_noRoot (hQ : QuadAlg T t n) :
    (∀ z : A, z ≠ 0 → IsUnit z) ↔ ¬ ∃ β : K, β ^ 2 - t * β + n = 0 := by
  constructor
  · rintro hu ⟨β, hβ⟩
    obtain ⟨e, he, he0, he1⟩ := idem_of_root hQ hβ
    have h1e : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
    have h2 : 1 - e = 0 := ((hu e he0).mul_right_eq_zero).1 h1e
    exact he1 (sub_eq_zero.1 h2).symm
  · exact unit_of_noRoot hQ

end Quad

section Approx
variable {R K F : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup F] [Module K F] [Module R F] [IsScalarTower R K F] (v : HeightOneSpectrum R)

abbrev OOv : Subalgebra R K :=
  Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors

theorem mem_OOv (x : K) :
    x ∈ OOv (K := K) v ↔ ∃ (a s : R) (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R K a * (algebraMap R K s)⁻¹ := by
  first
  | exact Iff.rfl
  | exact Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField K _ _ (Localization v.asIdeal.primeCompl) x

theorem isDVR_OOv : IsDiscreteValuationRing (OOv (K := K) v) := by
  haveI := Localization.subalgebra.isLocalization_ofField K v.asIdeal.primeCompl
    v.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _

theorem alg_ne_zero {s : R} (hs : s ∉ v.asIdeal) : algebraMap R K s ≠ 0 := by
  intro h0
  apply hs
  have h1 : s = 0 := IsFractionRing.injective R K (h0.trans (map_zero _).symm)
  rw [h1]
  exact zero_mem _

theorem val_alg (k : K) : Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  v.valuedAdicCompletion_eq_valuation' k

theorem mem_OOv_of_val {a : K} (h : v.valuation K a ≤ 1) : a ∈ OOv (K := K) v := by
  have h1 : a ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v).toSubring := by
    show a ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (Valuation.mem_valuationSubring_iff _ _).2 h
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h1
  exact h1

theorem exists_inv_mod (n : ℕ) {s : R} (hs : s ∉ v.asIdeal) : ∃ t : R, 1 - s * t ∈ v.asIdeal ^ n := by
  have h1 : Ideal.span {s} ⊔ v.asIdeal = ⊤ := by
    by_contra hne
    have heq := v.isMaximal.eq_of_le hne (le_sup_right : v.asIdeal ≤ Ideal.span {s} ⊔ v.asIdeal)
    apply hs
    rw [heq]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self s)
  have h2 : Ideal.span {s} ⊔ v.asIdeal ^ n = ⊤ := Ideal.sup_pow_eq_top h1
  have h3 : (1 : R) ∈ Ideal.span {s} ⊔ v.asIdeal ^ n := by rw [h2]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h3
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨t, ?_⟩
  have : 1 - s * t = z := by rw [← hyz]; ring
  rw [this]
  exact hz

theorem approx (c : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ r : R, Valued.v ((c : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤
      WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  set p : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K π) with hp
  have hpv : Valued.v p = WithZero.exp (-1 : ℤ) := by
    rw [hp, val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hpn : Valued.v (p ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hpv, ← WithZero.exp_nsmul]; congr 1; simp
  have hopen : IsOpen {x : v.adicCompletion K |
      (x - (c : v.adicCompletion K)) * (p ^ n)⁻¹ ∈ (Valued.v.valuationSubring : ValuationSubring (v.adicCompletion K))} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      ((continuous_sub_right _).mul continuous_const)
  obtain ⟨k, hk⟩ := (v.denseRange_algebraMap K).exists_mem_open hopen ⟨c, by simp⟩
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - (c : v.adicCompletion K)) ≤ WithZero.exp (-(n : ℤ)) := by
    have h1 : Valued.v ((algebraMap K (v.adicCompletion K) k - (c : v.adicCompletion K)) * (p ^ n)⁻¹) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff _ _).1 hk
    rw [map_mul, map_inv₀, hpn] at h1
    have h2 := mul_le_mul' h1 (le_refl (WithZero.exp (-(n : ℤ))))
    rwa [mul_assoc, inv_mul_cancel₀ WithZero.exp_ne_zero, mul_one, one_mul] at h2
  have hle1 : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← val_alg]
    have e : algebraMap K (v.adicCompletion K) k = (algebraMap K (v.adicCompletion K) k - c) + c := by ring
    rw [e]
    exact Valuation.map_add_le _ (hk'.trans hle1) ((HeightOneSpectrum.mem_adicCompletionIntegers R K v).1 c.2)
  obtain ⟨a, s, hs, rfl⟩ := (mem_OOv v k).mp (mem_OOv_of_val v hk1)
  obtain ⟨t, ht⟩ := exists_inv_mod v n hs
  refine ⟨a * t, ?_⟩
  have hs0 := alg_ne_zero (K := K) v hs
  have e1 : algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t) =
      algebraMap R K a * algebraMap R K (1 - s * t) * (algebraMap R K s)⁻¹ := by
    simp only [map_mul, map_sub, map_one]
    field_simp
  have h2 : v.valuation K (algebraMap R K s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (v.intValuation_eq_one_iff_mem_primeCompl s).2 hs
  have h3 : v.valuation K (algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [e1, map_mul, map_mul, map_inv₀, h2, inv_one, mul_one]
    calc v.valuation K (algebraMap R K a) * v.valuation K (algebraMap R K (1 - s * t))
        ≤ 1 * WithZero.exp (-(n : ℤ)) := by
          refine mul_le_mul' (v.valuation_le_one a) ?_
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact (v.intValuation_le_pow_iff_mem _ n).2 ht
      _ = _ := one_mul _
  have e2 : (c : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (algebraMap R K (a * t)) =
      -(algebraMap K (v.adicCompletion K) (algebraMap R K a * (algebraMap R K s)⁻¹) - c) +
        algebraMap K (v.adicCompletion K) (algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t)) := by
    rw [map_sub]; ring
  rw [e2]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [Valuation.map_neg]; exact hk'
  · rw [val_alg]; exact h3

end Approx

section Compl

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iotaR : 𝓞 F →+* v.adicCompletion F := (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)

theorem val_int (x : 𝓞 F) : Valued.v (iotaR v x) = v.intValuation x := by
  rw [iotaR, RingHom.comp_apply, val_alg, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]

theorem norm_int_lt_one (x : 𝓞 F) : ‖iotaR v x‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [Valued.toNormedField.norm_lt_one_iff, val_int, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem norm_int_le_one (x : 𝓞 F) : ‖iotaR v x‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, val_int]
  exact v.intValuation_le_one x

theorem norm_int_eq_one (x : 𝓞 F) (hx : x ∉ v.asIdeal) : ‖iotaR v x‖ = 1 :=
  le_antisymm (norm_int_le_one v x) (not_lt.1 fun h => hx ((norm_int_lt_one v x).1 h))

theorem norm_four_le : ‖(4 : v.adicCompletion F)‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_natCast_le_one (v.adicCompletion F) 4
  exact_mod_cast h

theorem approx_one (β : v.adicCompletion F) (hβ : ‖β‖ ≤ 1) : ∃ b : 𝓞 F, ‖β - iotaR v b‖ < 1 := by
  have hβ' : Valued.v β ≤ 1 := Valued.toNormedField.norm_le_one_iff.1 hβ
  obtain ⟨r, hr⟩ := approx (K := F) v ⟨β, hβ'⟩ 1
  refine ⟨r, Valued.toNormedField.norm_lt_one_iff.2 (lt_of_le_of_lt hr ?_)⟩
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

end Compl

theorem nsub_le {K : Type*} [NormedField K] [IsUltrametricDist K] (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem root_norm_le {K : Type*} [NormedField K] [IsUltrametricDist K] {tr nm β : K} (htr : ‖tr‖ ≤ 1)
    (hnm : ‖nm‖ ≤ 1) (h : β ^ 2 - tr * β + nm = 0) : ‖β‖ ≤ 1 := by
  by_contra hb
  push_neg at hb
  have h1 : β ^ 2 = tr * β - nm := by linear_combination h
  have hn : ‖β‖ ^ 2 ≤ max (‖tr‖ * ‖β‖) ‖nm‖ := by
    rw [← norm_pow, h1, ← norm_mul]
    exact nsub_le _ _
  have hb0 : 0 ≤ ‖β‖ := norm_nonneg β
  have ht0 : 0 ≤ ‖tr‖ := norm_nonneg tr
  rcases le_max_iff.1 hn with h2 | h2 <;> nlinarith

section Host

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (p : PlF D) {θ : D.host.E} {c tr nm : 𝓞 D.host.F}

structure ThetaAt (p : PlF D) (θ : D.host.E) (c tr nm : 𝓞 D.host.F) : Prop where
  int : IsIntegral ℤ θ
  hc : ((c : D.host.F) : D.host.E) = (θ - D.conjF θ) ^ 2
  hcp : c ∉ p.asIdeal
  htr : ((tr : D.host.F) : D.host.E) = θ + D.conjF θ
  hnm : ((nm : D.host.F) : D.host.E) = θ * D.conjF θ

theorem thetaAt_exists : ∃ θ c tr nm, ThetaAt p θ c tr nm := by
  obtain ⟨θ, c, tr, nm, h1, h2, h3, h4, h5⟩ := Formalism.L2.SG.Pf.LocUnramP.exists_theta (p := p)
  exact ⟨θ, c, tr, nm, ⟨h1, h2, h3, h4, h5⟩⟩

variable {p}

def thO (h : ThetaAt p θ c tr nm) : 𝓞 D.host.E := ⟨θ, h.int⟩

theorem sigO_thO (h : ThetaAt p θ c tr nm) : ((sigO (thO h) : 𝓞 D.host.E) : D.host.E) = D.conjF θ := by
  rw [Formalism.MainNotions.LocalModelPeriodLattices.conjF_eq_complexConj]
  rfl

theorem disc_O (h : ThetaAt p θ c tr nm) : tr ^ 2 - 4 * nm = c := by
  have hinj : Function.Injective (fun x : 𝓞 D.host.F => ((x : D.host.F) : D.host.E)) :=
    Subtype.val_injective.comp RingOfIntegers.coe_injective
  rw [show tr ^ 2 - 4 * nm = tr ^ 2 - (nm + nm + nm + nm) by ring]
  apply hinj
  simp only
  push_cast
  rw [h.hc, h.htr, h.hnm]
  ring

theorem prod_eq (h : ThetaAt p θ c tr nm) (b : 𝓞 D.host.F) :
    (thO h - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b) * (sigO (thO h) - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (b ^ 2 - tr * b + nm) := by
  apply RingOfIntegers.coe_injective
  have hb : ∀ z : 𝓞 D.host.F,
      ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) z : 𝓞 D.host.E) : D.host.E) = ((z : D.host.F) : D.host.E) :=
    fun z => rfl
  push_cast [hb, sigO_thO h]
  rw [h.htr, h.hnm]
  show (θ - _) * (D.conjF θ - _) = _
  ring

theorem c_eq_O (h : ThetaAt p θ c tr nm) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c = (thO h - sigO (thO h)) ^ 2 := by
  apply RingOfIntegers.coe_injective
  have hb : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) =
      ((c : D.host.F) : D.host.E) := rfl
  rw [hb, h.hc, map_pow, map_sub]
  show _ = ((thO h : D.host.E) - ((sigO (thO h) : 𝓞 D.host.E) : D.host.E)) ^ 2
  rw [sigO_thO h]
  rfl

theorem sigO_sigO (x : 𝓞 D.host.E) : sigO (sigO x) = x := by
  apply RingOfIntegers.coe_injective
  simp [sigO]

theorem not_prime_of_root (h : ThetaAt p θ c tr nm) (β : p.adicCompletion D.host.F)
    (hβ : β ^ 2 - iotaR p tr * β + iotaR p nm = 0) :
    ¬ (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := by
  intro hpr
  have hb1 : ‖β‖ ≤ 1 := root_norm_le (norm_int_le_one p tr) (norm_int_le_one p nm) hβ
  obtain ⟨b, hb⟩ := approx_one p β hb1
  have hfb : b ^ 2 - tr * b + nm ∈ p.asIdeal := by
    rw [← norm_int_lt_one p]
    have e : iotaR p (b ^ 2 - tr * b + nm) = (iotaR p b - β) * (iotaR p b + β - iotaR p tr) := by
      simp only [map_add, map_sub, map_mul, map_pow]
      linear_combination hβ
    rw [e, norm_mul]
    have h1 : ‖iotaR p b - β‖ < 1 := by rw [norm_sub_rev]; exact hb
    have h2 : ‖iotaR p b + β - iotaR p tr‖ ≤ 1 := by
      refine (nsub_le _ _).trans (max_le ?_ (norm_int_le_one p tr))
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le_one p b) hb1)
    calc ‖iotaR p b - β‖ * ‖iotaR p b + β - iotaR p tr‖ ≤ ‖iotaR p b - β‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h1
  set I := p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) with hI
  have hσI : ∀ z ∈ I, sigO z ∈ I := by
    have hmap : I.map ((sigO (D := D) : 𝓞 D.host.E →+* 𝓞 D.host.E)) = I := by
      rw [hI, Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => sigO_alg a
    intro z hz
    rw [← hmap]
    exact Ideal.mem_map_of_mem ((sigO (D := D) : 𝓞 D.host.E →+* 𝓞 D.host.E)) hz
  have hmem : (thO h - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b) *
      (sigO (thO h) - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b) ∈ I := by
    rw [prod_eq h b]; exact Ideal.mem_map_of_mem _ hfb
  have h1 : thO h - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ I ∧
      sigO (thO h) - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ I := by
    rcases hpr.mem_or_mem hmem with h' | h'
    · refine ⟨h', ?_⟩
      have := hσI _ h'
      rwa [map_sub, sigO_alg] at this
    · refine ⟨?_, h'⟩
      have := hσI _ h'
      rwa [map_sub, sigO_sigO, sigO_alg] at this
  have h2 : thO h - sigO (thO h) ∈ I := by
    have := I.sub_mem h1.1 h1.2
    rwa [sub_sub_sub_cancel_right] at this
  have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ I := by
    rw [c_eq_O h]; exact Ideal.pow_mem_of_mem I h2 2 two_pos
  have : p.asIdeal.IsMaximal := p.isMaximal
  have hcomap : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal :=
    (p.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpr.ne_top) Ideal.le_comap_map).symm
  exact h.hcp (hcomap ▸ Ideal.mem_comap.2 h3)

theorem root_of_twoOver (h : ThetaAt p θ c tr nm) (h2 : TwoOver p.asIdeal) :
    ∃ β : p.adicCompletion D.host.F, β ^ 2 - iotaR p tr * β + iotaR p nm = 0 := by
  obtain ⟨P, Q, hPQ, hP, hQ, hPc, hQc⟩ := h2
  have : p.asIdeal.IsMaximal := p.isMaximal
  have hq0 := p.ne_bot
  have hP' : P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 D.host.E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hq0 _).2 ⟨hP, ⟨hPc.symm⟩⟩
  have hQ' : Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 D.host.E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hq0 _).2 ⟨hQ, ⟨hQc.symm⟩⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 D.host.E) D.host.F D.host.E hq0
  rw [Formalism.BasicNotions.Examples₂.finrank_FE D.host] at hsum
  have hpos : ∀ R ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 D.host.E),
      1 ≤ p.asIdeal.ramificationIdx' R * p.asIdeal.inertiaDeg' R := by
    intro R hR
    rw [IsDedekindDomain.mem_primesOverFinset_iff hq0] at hR
    obtain ⟨hRp, hRl⟩ := hR
    have he : p.asIdeal.ramificationIdx' R ≠ 0 := by
      refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ hRp ?_
      · exact Ideal.map_ne_bot_of_ne_bot hq0
      · rw [Ideal.map_le_iff_le_comap]; exact le_of_eq hRl.over
    have hf := Ideal.inertiaDeg'_pos p.asIdeal R
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')
  have hle : p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P +
      p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q ≤ 2 := by
    rw [← hsum]
    exact Finset.add_le_sum (f := fun R => p.asIdeal.ramificationIdx' R * p.asIdeal.inertiaDeg' R)
      (fun _ _ => Nat.zero_le _) hP' hQ' hPQ
  have hPpos := hpos P hP'
  have hQpos := hpos Q hQ'
  have hef : p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P = 1 := by omega
  have hf1 : p.asIdeal.inertiaDeg' P = 1 := Nat.eq_one_of_mul_eq_one_left hef
  have : P.LiesOver p.asIdeal := ⟨hPc.symm⟩
  have : P.IsPrime := hP
  rw [Ideal.inertiaDeg_algebraMap] at hf1
  letI : Field (𝓞 D.host.F ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one hf1
  have hmem : Ideal.Quotient.mk P (thO h) ∈ (⊥ : Subalgebra (𝓞 D.host.F ⧸ p.asIdeal) (𝓞 D.host.E ⧸ P)) := by
    rw [hbt]; trivial
  obtain ⟨c', hc'⟩ := Algebra.mem_bot.1 hmem
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hc'
  have ha : thO h - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P := by
    rw [← Ideal.Quotient.eq]; exact hc'.symm
  have hfa : a ^ 2 - tr * a + nm ∈ p.asIdeal := by
    rw [← hPc, Ideal.mem_comap, ← prod_eq h a]
    exact P.mul_mem_right _ ha
  have hdisc : iotaR p tr ^ 2 - 4 * iotaR p nm = iotaR p c := by
    rw [← disc_O h]; simp only [map_sub, map_mul, map_pow, map_ofNat]
  have ha0 : ‖iotaR p a ^ 2 - iotaR p tr * iotaR p a + iotaR p nm‖ < 1 := by
    have e : iotaR p a ^ 2 - iotaR p tr * iotaR p a + iotaR p nm = iotaR p (a ^ 2 - tr * a + nm) := by
      simp only [map_add, map_sub, map_mul, map_pow]
    rw [e, norm_int_lt_one]
    exact hfa
  exact newton_quad _ _ _ hdisc (norm_int_eq_one p c h.hcp) (norm_four_le p) _ ha0

theorem root_iff (h : ThetaAt p θ c tr nm) :
    (∃ β : p.adicCompletion D.host.F, β ^ 2 - iotaR p tr * β + iotaR p nm = 0) ↔
      ¬ (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime :=
  ⟨fun ⟨β, hβ⟩ => not_prime_of_root h β hβ, fun hn => root_of_twoOver h ((twoOver_iff p).2 hn)⟩

end Host

section TensHost

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {p : PlF D} {θ : D.host.E} {c tr nm : 𝓞 D.host.F}

theorem theta_notF (h : ThetaAt p θ c tr nm) (a : D.host.F) : θ ≠ algebraMap D.host.F D.host.E a := by
  intro hθ
  apply h.hcp
  have h0 : ((c : D.host.F) : D.host.E) = 0 := by
    rw [h.hc, hθ, AlgHom.commutes, sub_self]
    ring
  have hc0 : c = 0 := by
    apply RingOfIntegers.coe_injective
    apply Subtype.val_injective
    simpa using h0
  rw [hc0]
  exact zero_mem _

theorem li_theta (h : ThetaAt p θ c tr nm) : LinearIndependent D.host.F ![(1 : D.host.E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, rfl⟩
  · exfalso
    apply theta_notF h (-(s / t))
    rw [Algebra.algebraMap_eq_smul_one]
    have : t • θ = -(s • (1 : D.host.E)) := eq_neg_of_add_eq_zero_right hst
    calc θ = t⁻¹ • (t • θ) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = -(s / t) • (1 : D.host.E) := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

def basE (h : ThetaAt p θ c tr nm) : Module.Basis (Fin 2) D.host.F D.host.E :=
  basisOfLinearIndependentOfCardEqFinrank (li_theta h) (by rw [Fintype.card_fin, Formalism.BasicNotions.Examples₂.finrank_FE D.host])

theorem basE_apply (h : ThetaAt p θ c tr nm) (i : Fin 2) : basE h i = ![(1 : D.host.E), θ] i := by
  simp [basE]

def basA (h : ThetaAt p θ c tr nm) :
    Module.Basis (Fin 2) (p.adicCompletion D.host.F) (p.adicCompletion D.host.F ⊗[D.host.F] D.host.E) :=
  Algebra.TensorProduct.basis (p.adicCompletion D.host.F) (basE h)

theorem basA_zero (h : ThetaAt p θ c tr nm) : basA h 0 = 1 := by
  rw [basA, Algebra.TensorProduct.basis_apply, basE_apply]
  rfl

theorem basA_one (h : ThetaAt p θ c tr nm) : basA h 1 = (1 : p.adicCompletion D.host.F) ⊗ₜ θ := by
  rw [basA, Algebra.TensorProduct.basis_apply, basE_apply]
  rfl

theorem tens_one (a : D.host.F) :
    (1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E a) =
      algebraMap (p.adicCompletion D.host.F) (p.adicCompletion D.host.F ⊗[D.host.F] D.host.E)
        (algebraMap D.host.F (p.adicCompletion D.host.F) a) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one a,
    Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp

theorem tens_alg (a : D.host.F) (y : D.host.E) :
    (1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E a * y) =
      algebraMap (p.adicCompletion D.host.F) (p.adicCompletion D.host.F ⊗[D.host.F] D.host.E)
        (algebraMap D.host.F (p.adicCompletion D.host.F) a) * ((1 : p.adicCompletion D.host.F) ⊗ₜ y) := by
  rw [← tens_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tens_sq (h : ThetaAt p θ c tr nm) :
    ((1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] θ) * ((1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] θ) =
      (1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F]
        (algebraMap D.host.F D.host.E (tr : D.host.F) * θ - algebraMap D.host.F D.host.E (nm : D.host.F)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  have e1 : algebraMap D.host.F D.host.E (tr : D.host.F) = ((tr : D.host.F) : D.host.E) := rfl
  have e2 : algebraMap D.host.F D.host.E (nm : D.host.F) = ((nm : D.host.F) : D.host.E) := rfl
  rw [e1, e2, h.htr, h.hnm]
  ring

theorem tens_rel (h : ThetaAt p θ c tr nm) :
    ((1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] θ) * ((1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] θ) =
      algebraMap (p.adicCompletion D.host.F) (p.adicCompletion D.host.F ⊗[D.host.F] D.host.E) (iotaR p tr) *
          ((1 : p.adicCompletion D.host.F) ⊗ₜ[D.host.F] θ) -
        algebraMap (p.adicCompletion D.host.F) (p.adicCompletion D.host.F ⊗[D.host.F] D.host.E) (iotaR p nm) := by
  rw [tens_sq h, TensorProduct.tmul_sub, tens_alg, tens_one]
  rfl

theorem quadAlg_tens (h : ThetaAt p θ c tr nm) :
    QuadAlg (A := p.adicCompletion D.host.F ⊗[D.host.F] D.host.E) ((1 : p.adicCompletion D.host.F) ⊗ₜ θ)
      (iotaR p tr) (iotaR p nm) where
  span z := by
    refine ⟨(basA h).repr z 0, (basA h).repr z 1, ?_⟩
    have hs := (basA h).sum_repr z
    rw [Fin.sum_univ_two, basA_zero, basA_one] at hs
    exact hs.symm
  indep x y hxy := by
    have hli := Fintype.linearIndependent_iff.1 (basA h).linearIndependent ![x, y] (by
      rw [Fin.sum_univ_two, basA_zero, basA_one]
      exact hxy)
    exact ⟨hli 0, hli 1⟩
  rel := tens_rel h
  disc := by
    have e : iotaR p tr ^ 2 - 4 * iotaR p nm = iotaR p c := by
      rw [← disc_O h]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e]
    intro h0
    have := norm_int_eq_one p c h.hcp
    rw [h0, norm_zero] at this
    exact zero_ne_one this

theorem idem_iff_notPrime (p : PlF D) :
    IdemNT (p.adicCompletion D.host.F ⊗[D.host.F] D.host.E) ↔
      ¬ (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := by
  obtain ⟨θ, c, tr, nm, h⟩ := thetaAt_exists p
  rw [idem_iff_root (quadAlg_tens h)]
  exact root_iff h

theorem unit_iff_prime (p : PlF D) :
    (∀ z : p.adicCompletion D.host.F ⊗[D.host.F] D.host.E, z ≠ 0 → IsUnit z) ↔
      (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := by
  obtain ⟨θ, c, tr, nm, h⟩ := thetaAt_exists p
  rw [field_iff_noRoot (quadAlg_tens h), root_iff h, not_not]

end TensHost

section Final

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem etaF_holds : EtaF X := by
  intro v
  have hjk : ∀ a : X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E a) =
      algebraMap D.host.F D.host.E (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X a) :=
    fun a => (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF_coe X a).symm
  have h1 := idemNT_iff (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) X.ιE hjk v
  have hiff : IdemNT (v.adicCompletion X.B.I.F ⊗[X.B.I.F] X.B.I.E) ↔
      ¬ ((plEquiv X v).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime :=
    h1.trans (idem_iff_notPrime (plEquiv X v))
  unfold Formalism.L2.SG.LocVol.etaV Formalism.HermitianLattices.Ext.L3.etaF
  split_ifs with ha hb hb
  · exact absurd hb (hiff.1 ha)
  · simp
  · simp
  · exact absurd (hiff.2 hb) ha

theorem fieldDict_holds (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' :=
  fieldDict_of_eta X (etaF_holds X) u u'

theorem etaLoc_of_tied (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) (p : PlF D) :
    (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then (-1 : ℝ) else 1) =
      Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F p.asIdeal := by
  have h1 : (∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x) ↔
      (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := by
    rw [← unit_iff_prime p]
    obtain ⟨e⟩ := hL p
    constructor
    · intro h z hz
      have h2 := h (e.eE.symm z) ((map_ne_zero_iff _ e.eE.symm.injective).2 hz)
      have h4 := h2.map e.eE
      erw [RingEquiv.apply_symm_apply] at h4
      exact h4
    · intro h x hx
      have h2 := h (e.eE x) ((map_ne_zero_iff _ e.eE.injective).2 hx)
      have h4 := h2.map e.eE.symm
      erw [RingEquiv.symm_apply_apply] at h4
      exact h4
  unfold Formalism.HermitianLattices.Ext.L3.etaF
  by_cases hp : (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime
  · rw [if_pos (h1.2 hp), if_pos hp]
  · rw [if_neg (mt h1.1 hp), if_neg hp]

end Final

end Formalism.L2.SG.Pf.AlTieLG
