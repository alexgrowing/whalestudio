import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogEmbeddingsEqNorm
import Development.WeilBound.CoreStatements.SesquilinearFractions.NPlaces
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.Dd

variable {K : Type} [Field K] [NumberField K] {p : Nat.Primes}

theorem norm_int_le (κ : K →+* ℂ_[p]) (x : 𝓞 K) : ‖κ (algebraMap (𝓞 K) K x)‖ ≤ 1 :=
  PositivityTheory.Xgf.NI.norm_int_le (κ.comp (algebraMap (𝓞 K) K)) x

theorem norm_natCast_lt_one_iff (n : ℕ) : ‖(n : ℂ_[p])‖ < 1 ↔ (p : ℕ) ∣ n := by
  have h : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((n : ℚ) : ℚ_[p]) := by simp
  rw [h, norm_algebraMap', Padic.eq_padicNorm]
  exact_mod_cast padicNorm.nat_lt_one_iff n

def ballIdeal (κ : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {x | ‖κ (algebraMap (𝓞 K) K x)‖ < 1}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le κ c)).trans_lt hx

theorem mem_ballIdeal (κ : K →+* ℂ_[p]) (x : 𝓞 K) :
    x ∈ ballIdeal κ ↔ ‖κ (algebraMap (𝓞 K) K x)‖ < 1 := Iff.rfl

theorem natCast_mem_ballIdeal (κ : K →+* ℂ_[p]) : ((p : ℕ) : 𝓞 K) ∈ ballIdeal κ := by
  rw [mem_ballIdeal, map_natCast, map_natCast]
  exact (norm_natCast_lt_one_iff _).2 dvd_rfl

def placeOf (κ : K →+* ℂ_[p]) : HeightOneSpectrum (𝓞 K) where
  asIdeal := ballIdeal κ
  isPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have : (1 : 𝓞 K) ∈ ballIdeal κ := h ▸ Submodule.mem_top
      simp [mem_ballIdeal] at this
    · by_contra hn
      push_neg at hn
      rw [mem_ballIdeal, mem_ballIdeal, not_lt, not_lt] at hn
      rw [mem_ballIdeal, map_mul, map_mul, norm_mul] at hab
      have h1 := le_antisymm (norm_int_le κ a) hn.1
      have h2 := le_antisymm (norm_int_le κ b) hn.2
      rw [h1, h2] at hab
      simp at hab
  ne_bot := fun h => by
    have h1 := natCast_mem_ballIdeal (K := K) κ
    rw [show ballIdeal κ = ⊥ from h, Ideal.mem_bot] at h1
    exact p.2.ne_zero (by exact_mod_cast h1)

theorem natCast_mem_placeOf (κ : K →+* ℂ_[p]) : ((p : ℕ) : 𝓞 K) ∈ (placeOf κ).asIdeal :=
  natCast_mem_ballIdeal κ

theorem val_lt_one_iff (la : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    la.valuation K (algebraMap (𝓞 K) K r) < 1 ↔ r ∈ la.asIdeal :=
  la.valuation_lt_one_iff_mem r

theorem val_algebraMap (la : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    la.valuation K (algebraMap (𝓞 K) K r) = la.intValuation r :=
  la.valuation_of_algebraMap r

theorem exists_frac (la : HeightOneSpectrum (𝓞 K)) (a : K) (h : la.valuation K a ≤ 1) :
    ∃ c z : 𝓞 K, z ∉ la.asIdeal ∧ a * algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K c := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
  have hsp : Ideal.span {d} ≠ 0 := by simpa [Ideal.zero_eq_bot] using hd0
  obtain ⟨m, B, hB, hs⟩ := WfDvdMonoid.max_power_factor hsp la.irreducible
  obtain ⟨z, hzB, hzl⟩ := SetLike.not_le_iff_exists.1 (fun h' => hB (Ideal.dvd_iff_le.2 h'))
  have hdm : d ∈ la.asIdeal ^ m := by
    have h1 : d ∈ Ideal.span {d} := Ideal.mem_span_singleton_self d
    rw [hs] at h1
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  have hv : la.intValuation n ≤ la.intValuation d := by
    have hv0 : 0 < la.valuation K (algebraMap (𝓞 K) K d) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hd1)
    rwa [map_div₀, div_le_one₀ hv0, val_algebraMap, val_algebraMap] at h
  have hnm : n ∈ la.asIdeal ^ m := by
    rw [← la.intValuation_le_pow_iff_mem]
    exact hv.trans ((la.intValuation_le_pow_iff_mem d m).2 hdm)
  have h2 : n * z ∈ Ideal.span {d} := by
    rw [hs]; exact Ideal.mul_mem_mul hnm hzB
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨c, z, hzl, ?_⟩
  have h3 := congrArg (algebraMap (𝓞 K) K) hc
  rw [map_mul, map_mul] at h3
  field_simp
  rw [← h3, mul_comm]

def Lies (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1

theorem lies_placeOf (κ : K →+* ℂ_[p]) : Lies κ (placeOf κ) := by
  have hunit : ∀ z : 𝓞 K, z ∉ (placeOf κ).asIdeal → ‖κ (algebraMap (𝓞 K) K z)‖ = 1 := fun z hz =>
    le_antisymm (norm_int_le κ z) (not_lt.1 hz)
  intro a
  constructor
  · intro h
    obtain ⟨c, z, hz, e⟩ := exists_frac _ a h
    have h1 := congrArg (fun t => ‖κ t‖) e
    simp only [map_mul, norm_mul, hunit z hz, mul_one] at h1
    rw [h1]; exact norm_int_le κ c
  · intro h
    by_contra hv
    rw [not_le] at hv
    have ha : a ≠ 0 := by rintro rfl; simp at hv
    have hinv : (placeOf κ).valuation K a⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv
    obtain ⟨c, z, hz, e⟩ := exists_frac _ a⁻¹ hinv.le
    have hzv : (placeOf κ).valuation K (algebraMap (𝓞 K) K z) = 1 :=
      le_antisymm ((placeOf κ).valuation_le_one z)
        (not_lt.1 fun h' => hz ((val_lt_one_iff _ z).1 h'))
    have hc : c ∈ (placeOf κ).asIdeal := (val_lt_one_iff _ c).1 (by
      rw [← e, map_mul, hzv, mul_one]; exact hinv)
    have hcn : ‖κ (algebraMap (𝓞 K) K c)‖ < 1 := hc
    have h1 := congrArg (fun t => ‖κ t‖) e
    simp only [map_mul, norm_mul, hunit z hz, mul_one, map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖κ a‖ := norm_pos_iff.2 ((map_ne_zero κ).2 ha)
    have h2 : 1 < ‖κ a‖ := (inv_lt_one₀ hpos).1 (h1 ▸ hcn)
    linarith

theorem Lies.norm_lt_one_iff {κ : K →+* ℂ_[p]} {la : HeightOneSpectrum (𝓞 K)} (h : Lies κ la) (a : 𝓞 K) :
    ‖κ (algebraMap (𝓞 K) K a)‖ < 1 ↔ a ∈ la.asIdeal := by
  rw [← val_lt_one_iff la a]
  by_cases ha : algebraMap (𝓞 K) K a = 0
  · rw [ha]; simp
  · have h1 := h (algebraMap (𝓞 K) K a)⁻¹
    have hv0 : 0 < la.valuation K (algebraMap (𝓞 K) K a) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)
    have hn0 : 0 < ‖κ (algebraMap (𝓞 K) K a)‖ := norm_pos_iff.2 ((map_ne_zero κ).2 ha)
    rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hv0, inv_le_one₀ hn0] at h1
    rw [← not_le, ← not_le, h1]

theorem Lies.eq_placeOf {κ : K →+* ℂ_[p]} {la : HeightOneSpectrum (𝓞 K)} (h : Lies κ la) : la = placeOf κ :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (h.norm_lt_one_iff x).symm)

theorem Lies.norm_le_of_val_le {κ : K →+* ℂ_[p]} {la : HeightOneSpectrum (𝓞 K)} (h : Lies κ la) {a b : K}
    (hb : b ≠ 0) (hv : la.valuation K a ≤ la.valuation K b) : ‖κ a‖ ≤ ‖κ b‖ := by
  have h0 : 0 < la.valuation K b := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb)
  have h1 : la.valuation K (a / b) ≤ 1 := by rwa [map_div₀, div_le_one₀ h0]
  have h2 := (h _).1 h1
  rwa [map_div₀, norm_div, div_le_one₀ (norm_pos_iff.2 ((map_ne_zero κ).2 hb))] at h2

theorem ne_zero_of_unif {la : HeightOneSpectrum (𝓞 K)} {π : K}
    (hπ : la.valuation K π = WithZero.exp (-1 : ℤ)) : π ≠ 0 := by
  rintro rfl
  rw [map_zero] at hπ
  exact WithZero.exp_ne_zero hπ.symm

theorem Lies.norm_unif_eq {κ : K →+* ℂ_[p]} {la : HeightOneSpectrum (𝓞 K)} (h : Lies κ la) {π π' : K}
    (hπ : la.valuation K π = WithZero.exp (-1 : ℤ)) (hπ' : la.valuation K π' = WithZero.exp (-1 : ℤ)) :
    ‖κ π‖ = ‖κ π'‖ :=
  le_antisymm (h.norm_le_of_val_le (ne_zero_of_unif hπ') (hπ.trans hπ'.symm).le)
    (h.norm_le_of_val_le (ne_zero_of_unif hπ) (hπ'.trans hπ.symm).le)

theorem finite_over {l : ℕ} (hl : l ≠ 0) : {w : HeightOneSpectrum (𝓞 K) | (l : 𝓞 K) ∈ w.asIdeal}.Finite := by
  have h0 : Ideal.span {(l : 𝓞 K)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using hl
  exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.2 hw

theorem exists_sep (la : HeightOneSpectrum (𝓞 K)) (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) :
    ∃ y : 𝓞 K, la.intValuation y = WithZero.exp (-1 : ℤ) ∧
      ∀ q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ q.asIdeal → q ≠ la → y ∉ q.asIdeal := by
  classical
  obtain ⟨u, hu⟩ := la.intValuation_exists_uniformizer
  have hf := finite_over (K := K) (l := (p : ℕ)) p.2.ne_zero
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hf.toFinset)
    (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) (fun q => if q = la then 2 else 1)
    (fun q _ => q.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun q => if q.1 = la then u else 1)
  refine ⟨y, ?_, fun q hq hne hmem => ?_⟩
  · have h1 := hy la (by simpa using hp)
    simp only [if_true] at h1
    have h2 : la.intValuation (y - u) < la.intValuation u := by
      rw [hu]
      refine ((la.intValuation_le_pow_iff_mem _ 2).2 h1).trans_lt ?_
      rw [WithZero.exp_lt_exp]; norm_num
    have h3 := la.intValuation.map_add_eq_of_lt_right (x := y - u) (y := u) h2
    rw [sub_add_cancel] at h3
    rw [h3, hu]
  · have h1 := hy q (by simpa using hq)
    simp only [if_neg hne, pow_one] at h1
    have h2 : (1 : 𝓞 K) ∈ q.asIdeal := by
      have := q.asIdeal.sub_mem hmem h1
      simpa using this
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem exists_quot (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I ≠ 0) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ Ideal.absNorm I) : ∃ x : 𝓞 K ⧸ I, x ≠ 0 ∧ (l : 𝓞 K ⧸ I) * x = 0 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hI hd
  haveI := Nat.finite_of_card_ne_zero hI
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hd
  refine ⟨x, fun h => ?_, ?_⟩
  · rw [h, addOrderOf_zero] at hx; exact hl.one_lt.ne hx
  · rw [← nsmul_eq_mul, ← hx]; exact addOrderOf_nsmul_eq_zero x

theorem absNorm_eq_pow (la : HeightOneSpectrum (𝓞 K)) (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) :
    Ideal.absNorm la.asIdeal = (p : ℕ) ^ (Ideal.absNorm la.asIdeal).primeFactorsList.length := by
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine Nat.eq_prime_pow_of_unique_prime_dvd h0 fun {l} hl hd => ?_
  obtain ⟨x, hx0, hx⟩ := exists_quot la.asIdeal h0 hl hd
  haveI := la.isPrime
  have hl0 : ((l : 𝓞 K) : 𝓞 K ⧸ la.asIdeal) = 0 := (mul_eq_zero.1 hx).resolve_right hx0
  have hlm : (l : 𝓞 K) ∈ la.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using hl0
  exact congrArg Subtype.val (PositivityTheory.Xgf.NP.prime_unique la (p := ⟨l, hl⟩) hlm hp)

theorem norm_natCast_p : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  have h : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((p : ℕ) : ℚ_[p]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]

theorem norm_absNorm_place (la : HeightOneSpectrum (𝓞 K)) (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) :
    ‖((Ideal.absNorm la.asIdeal : ℕ) : ℂ_[p])‖ = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [absNorm_eq_pow la hp, Nat.cast_pow, Nat.cast_pow, norm_pow, norm_natCast_p, inv_pow]

theorem norm_absNorm_coprime (J : Ideal (𝓞 K)) (hJ : Ideal.absNorm J ≠ 0) {j s : 𝓞 K} (hj : j ∈ J)
    (e : j + s * ((p : ℕ) : 𝓞 K) = 1) : ‖((Ideal.absNorm J : ℕ) : ℂ_[p])‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one _ _) (not_lt.1 fun h => ?_)
  obtain ⟨x, hx0, hx⟩ := exists_quot J hJ p.2 ((norm_natCast_lt_one_iff _).1 h)
  apply hx0
  have hj0 : (j : 𝓞 K ⧸ J) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hj
  have e' := congrArg (Ideal.Quotient.mk J) e
  rw [map_add, map_mul, map_one] at e'
  calc x = (Ideal.Quotient.mk J j + Ideal.Quotient.mk J s * Ideal.Quotient.mk J ((p : ℕ) : 𝓞 K)) * x := by
          rw [e', one_mul]
    _ = 0 := by
          rw [show Ideal.Quotient.mk J j = (j : 𝓞 K ⧸ J) from rfl, hj0, zero_add, mul_assoc, map_natCast, hx,
            mul_zero]

theorem norm_intCast_eq (n : ℤ) : ‖(n : ℂ_[p])‖ = ‖((n.natAbs : ℕ) : ℂ_[p])‖ := by
  rcases Int.natAbs_eq n with h | h
  · conv_lhs => rw [h]
    simp
  · conv_lhs => rw [h]
    simp

theorem norm_sep (la : HeightOneSpectrum (𝓞 K)) (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) (y : 𝓞 K)
    (hy1 : la.intValuation y = WithZero.exp (-1 : ℤ))
    (hy2 : ∀ q : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ q.asIdeal → q ≠ la → y ∉ q.asIdeal) :
    ‖((Algebra.norm ℚ (algebraMap (𝓞 K) K y) : ℚ) : ℂ_[p])‖ = ((Ideal.absNorm la.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hyl : y ∈ la.asIdeal := by
    rw [← la.intValuation_lt_one_iff_mem, hy1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hyl2 : y ∉ la.asIdeal ^ 2 := by
    rw [← la.intValuation_le_pow_iff_mem, hy1, WithZero.exp_le_exp]; norm_num
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 hyl
  have hy0 : y ≠ 0 := by rintro rfl; exact hyl2 (Ideal.zero_mem _)
  have hsp : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hy0
  have hJ0 : Ideal.absNorm J ≠ 0 := by
    rw [hJ, map_mul] at hsp; exact right_ne_zero_of_mul hsp
  have hcop : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by
    by_contra hn
    have hne : J ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} ≠ ⊤ := fun h => hn (h ▸ Submodule.mem_top)
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpM : ((p : ℕ) : 𝓞 K) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hJM : J ≤ M := le_sup_left.trans hle
    let q : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, fun h => by
      rw [h, Ideal.mem_bot] at hpM; exact p.2.ne_zero (by exact_mod_cast hpM)⟩
    have hyM : y ∈ la.asIdeal * J := by rw [← hJ]; exact Ideal.mem_span_singleton_self y
    by_cases hq : q = la
    · apply hyl2
      rw [pow_two]
      exact Ideal.mul_mono_right (show J ≤ la.asIdeal from hq ▸ hJM) hyM
    · exact hy2 q hpM hq (hJM ((Ideal.mul_le_inf.trans inf_le_right) hyM))
  obtain ⟨j, hj, t, ht, e⟩ := Submodule.mem_sup.1 hcop
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  have hN : (Algebra.norm ℚ (algebraMap (𝓞 K) K y) : ℚ) = ((Algebra.norm ℤ y : ℤ) : ℚ) :=
    (Algebra.coe_norm_int y).symm
  rw [hN, Rat.cast_intCast, norm_intCast_eq, ← Ideal.absNorm_span_singleton, hJ, map_mul, Nat.cast_mul,
    norm_mul, norm_absNorm_place la hp, norm_absNorm_coprime J hJ0 hj e, mul_one]

open Classical in

theorem sum_lies (la : HeightOneSpectrum (𝓞 K)) (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) {π : K}
    (hπ : la.valuation K π = WithZero.exp (-1 : ℤ)) :
    ∑ κ : K →+* ℂ_[p], (if placeOf κ = la then Real.log ‖κ π‖ else 0) =
      -Real.log (Ideal.absNorm la.asIdeal : ℝ) := by
  obtain ⟨y, hy1, hy2⟩ := exists_sep la hp
  have hyv : la.valuation K (algebraMap (𝓞 K) K y) = WithZero.exp (-1 : ℤ) := (val_algebraMap _ _).trans hy1
  have h1 := GlobalTheory.CompanionTheory.Ar.Fl.sum_log_norm_embeddings_eq_log_norm K ℂ_[p] _ (ne_zero_of_unif hyv)
  rw [norm_sep la hp y hy1 hy2, Real.log_inv] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs with h
  · subst h; exact congrArg Real.log ((lies_placeOf κ).norm_unif_eq hπ hyv)
  · have : y ∉ (placeOf κ).asIdeal := hy2 _ (natCast_mem_placeOf κ) h
    rw [le_antisymm (norm_int_le κ y) (not_lt.1 this), Real.log_one]

theorem deg_dict : ∀ (K : Type) [Field K] [NumberField K] (r : (K →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]), ∃ (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) ∧ la.valuation K π = WithZero.exp (-1 : ℤ)) ∧ (∃ N : LogNorms K, (∀ σ, N.inf σ = Real.log (r σ)) ∧ ∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation K π = WithZero.exp (-1 : ℤ) → N.fin p κ = ρ la * Real.log ‖κ π‖) ∧ ∀ N : LogNorms K, (∀ σ, N.inf σ = Real.log (r σ)) → (∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 K)) (π : K), (∀ a : K, la.valuation K a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation K π = WithZero.exp (-1 : ℤ) → N.fin p κ = ρ la * Real.log ‖κ π‖) → (N.IsAdelic ↔ (Function.support ρ).Finite) ∧ (N.IsAdelic → N.deg = GlobalTheory.FlatLine.lineDeg r ρ) := by
  intro K _ _ r ρ
  classical
  choose u hu using fun la : HeightOneSpectrum (𝓞 K) => la.valuation_exists_uniformizer K
  refine ⟨fun p κ => ⟨placeOf κ, u _, lies_placeOf κ, hu _⟩,
    ⟨⟨fun σ => Real.log (r σ), fun p κ => ρ (placeOf κ) * Real.log ‖κ (u (placeOf κ))‖⟩, fun σ => rfl,
      fun p κ la π hl hπ => ?_⟩, fun N hinf hfin => ?_⟩
  · obtain rfl := Lies.eq_placeOf (la := la) hl
    show ρ (placeOf κ) * Real.log ‖κ (u (placeOf κ))‖ = _
    rw [Lies.norm_unif_eq hl (hu _) hπ]
  have hf : ∀ (p : Nat.Primes) (κ : K →+* ℂ_[p]), N.fin p κ = ρ (placeOf κ) * Real.log ‖κ (u (placeOf κ))‖ :=
    fun p κ => hfin p κ _ _ (lies_placeOf κ) (hu _)
  choose P hP using PositivityTheory.Xgf.NP.exists_prime_mem (k := K)
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ la, ρ la ≠ 0 → la ∈ S) → ∀ p : Nat.Primes,
      N.finSum p = -∑ la ∈ S.filter (fun la => ((p : ℕ) : 𝓞 K) ∈ la.asIdeal),
        ρ la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := by
    intro S hS p
    have e1 : ∀ κ : K →+* ℂ_[p], N.fin p κ = ∑ la ∈ S.filter (fun la => ((p : ℕ) : 𝓞 K) ∈ la.asIdeal),
        ρ la * (if placeOf κ = la then Real.log ‖κ (u la)‖ else 0) := by
      intro κ
      rw [hf]
      by_cases hm : placeOf κ ∈ S
      · rw [Finset.sum_eq_single (placeOf κ)]
        · simp
        · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
        · intro hn; exact absurd (Finset.mem_filter.2 ⟨hm, natCast_mem_placeOf κ⟩) hn
      · have h0 : ρ (placeOf κ) = 0 := by by_contra h0; exact hm (hS _ h0)
        rw [h0, zero_mul]
        refine (Finset.sum_eq_zero fun la hla => ?_).symm
        have : placeOf κ ≠ la := fun h => hm (h ▸ (Finset.mem_filter.1 hla).1)
        rw [if_neg this, mul_zero]
    unfold LogNorms.finSum
    simp_rw [e1]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun la hla => ?_
    rw [← Finset.mul_sum, sum_lies la (Finset.mem_filter.1 hla).2 (hu la)]
    ring
  have hsupp : N.IsAdelic ↔ (Function.support ρ).Finite := by
    constructor
    · intro hA
      refine (Set.Finite.biUnion hA fun p _ => PositivityTheory.Xgf.NP.finite_over (k := K) p).subset ?_
      intro la hla
      simp only [Set.mem_iUnion]
      refine ⟨P la, ?_, hP la⟩
      have hs := sum_lies la (hP la) (hu la)
      have h1 : 1 < Ideal.absNorm la.asIdeal := by
        have h0 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
        have h1 : Ideal.absNorm la.asIdeal ≠ 1 := fun h => la.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
        omega
      have hne : ∑ κ : K →+* ℂ_[P la], (if placeOf κ = la then Real.log ‖κ (u la)‖ else 0) ≠ 0 := by
        rw [hs, neg_ne_zero]; exact (Real.log_pos (by exact_mod_cast h1)).ne'
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hpl : placeOf κ = la := by by_contra h; rw [if_neg h] at hκ; exact hκ rfl
      refine ⟨κ, ?_⟩
      rw [hf, hpl]
      exact mul_ne_zero hla (by rwa [if_pos hpl] at hκ)
    · intro hS
      refine (hS.image P).subset ?_
      rintro p ⟨κ, hκ⟩
      refine ⟨placeOf κ, fun h0 => hκ (by rw [hf, h0, zero_mul]), ?_⟩
      exact PositivityTheory.Xgf.NP.prime_unique _ (hP _) (natCast_mem_placeOf κ)
  refine ⟨hsupp, fun hA => ?_⟩
  have hS := hsupp.1 hA
  have hSm : ∀ la, ρ la ≠ 0 → la ∈ hS.toFinset := fun la h => hS.mem_toFinset.2 h
  have hsum : ∑ᶠ p, N.finSum p = -∑ la ∈ hS.toFinset, ρ la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := by
    rw [finsum_eq_sum_of_support_subset (s := hS.toFinset.image P)]
    · simp_rw [key _ hSm]
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (g := P) (t := hS.toFinset.image P)
        (fun la h => Finset.mem_image_of_mem P h)]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext la
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, PositivityTheory.Xgf.NP.prime_unique la (hP la) h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2 ▸ hP la⟩⟩
    · intro p hp
      rw [Function.mem_support, key _ hSm] at hp
      obtain ⟨la, hla, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (neg_ne_zero.1 hp)
      obtain ⟨hlaS, hpla⟩ := Finset.mem_filter.1 hla
      rw [Finset.coe_image]
      exact ⟨la, hlaS, PositivityTheory.Xgf.NP.prime_unique _ (hP la) hpla⟩
  have hl : ∑ᶠ la, ρ la * Formalism.BasicNotions.lw K la =
      (∑ la ∈ hS.toFinset, ρ la * Real.log (Ideal.absNorm la.asIdeal : ℝ)) / Module.finrank ℚ K := by
    rw [finsum_eq_sum_of_support_subset (s := hS.toFinset)]
    · rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun la _ => ?_
      simp only [Formalism.BasicNotions.lw]
      ring
    · intro la hla
      rw [Function.mem_support] at hla
      exact hSm la (left_ne_zero_of_mul hla)
  rw [LogNorms.deg, GlobalTheory.FlatLine.lineDeg, hl, hsum]
  simp only [hinf]
  ring

end GlobalTheory.CompanionTheory.Ar.Br.Dd
