import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationAlgebraMapEqCount

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing

noncomputable section

namespace GlobalTheory.Idele

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  first
  | exact @_root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count
  | exact _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count
  | (apply _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicValuationCountFactors.valuation_eq_exp_neg_count ..)

theorem le_of_count_le {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) :
    I ≤ J := by
  have hIJ : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have h1 : I * J⁻¹ ≤ 1 := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hIJ]
    refine finprod_induction (fun L : FractionalIdeal R⁰ K => L ≤ 1) le_rfl ?_ ?_
    · intro a b ha hb
      calc a * b ≤ 1 * b := by gcongr
        _ ≤ 1 := by simpa using hb
    · intro v
      have h0 : 0 ≤ FractionalIdeal.count K v (I * J⁻¹) := by
        rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
        linarith [h v]
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
      rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
  calc I = I * J⁻¹ * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := by gcongr
    _ = J := one_mul J

theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J :=
  le_antisymm (le_of_count_le hI hJ fun v => (h v).ge) (le_of_count_le hJ hI fun v => (h v).le)

theorem mem_iff_valuation_le {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ exp (-FractionalIdeal.count K v I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [FractionalIdeal.zero_mem]
  have hx' : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp_rw [fun v : HeightOneSpectrum R => valuation_eq_exp_neg_count v hx, exp_le_exp, neg_le_neg_iff]
  exact ⟨fun h v => FractionalIdeal.count_mono K v hx' h, le_of_count_le hx' hI⟩

theorem exists_mem_valuation_eq {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum R) :
    ∃ y ∈ I, v.valuation K y = exp (-FractionalIdeal.count K v I) := by
  classical
  by_contra hne
  push Not at hne
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := by simpa using v.ne_bot
  have hle : I ≤ (v.asIdeal : FractionalIdeal R⁰ K) * I := by
    intro y hy
    have hy' := (mem_iff_valuation_le hI y).1 hy
    refine (mem_iff_valuation_le (mul_ne_zero hv hI) y).2 fun w => ?_
    rw [FractionalIdeal.count_mul K w hv hI, FractionalIdeal.count_maximal]
    split_ifs with hw
    · subst hw
      have := lt_of_le_of_ne (hy' v) (hne y hy)
      rcases eq_or_ne (v.valuation K y) 0 with h0 | h0
      · simp [h0]
      rw [← exp_log h0, exp_lt_exp] at this
      rw [← exp_log h0, exp_le_exp]
      omega
    · simpa using hy' w
  have := FractionalIdeal.count_mono K v hI hle
  rw [FractionalIdeal.count_mul K v hv hI, FractionalIdeal.count_self] at this
  omega

def localIdeal (v : HeightOneSpectrum R) (I : FractionalIdeal R⁰ K) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Submodule.span _ (algebraMap K (v.adicCompletion K) '' (I : Set K))

theorem valued_algebraMap (v : HeightOneSpectrum R) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
  valuedAdicCompletion_eq_valuation' v x

theorem mem_localIdeal_iff {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (v : HeightOneSpectrum R)
    (x : v.adicCompletion K) :
    x ∈ localIdeal v I ↔ Valued.v x ≤ exp (-FractionalIdeal.count K v I) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [valued_algebraMap]
      exact (mem_iff_valuation_le hI y).1 hy v
    | zero => simp
    | add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans (max_le hx hy)
    | smul a x _ hx =>
      have ha : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
      change Valued.v ((a : v.adicCompletion K) * x) ≤ _
      rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans hx
  · intro hx
    obtain ⟨y, hy, hvy⟩ := exists_mem_valuation_eq hI v
    rw [← valued_algebraMap] at hvy
    have hy0 : Valued.v (algebraMap K (v.adicCompletion K) y) ≠ 0 := by rw [hvy]; exact exp_ne_zero
    have hy1 : algebraMap K (v.adicCompletion K) y ≠ 0 := by
      intro h; rw [h] at hy0; simp at hy0
    have hm : x / algebraMap K (v.adicCompletion K) y ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, div_le_one₀ (zero_lt_iff.2 hy0), hvy]
      exact hx
    have : x = (⟨_, hm⟩ : v.adicCompletionIntegers K) • algebraMap K (v.adicCompletion K) y := by
      change x = x / _ * _
      rw [div_mul_cancel₀ _ hy1]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)

theorem localIdeal_zero (v : HeightOneSpectrum R) :
    localIdeal v (0 : FractionalIdeal R⁰ K) = ⊥ := by
  rw [localIdeal, Submodule.span_eq_bot]
  rintro _ ⟨y, hy, rfl⟩
  rw [(FractionalIdeal.mem_zero_iff R⁰).1 hy, map_zero]

theorem mem_localIdeal_one_iff (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    x ∈ localIdeal v (1 : FractionalIdeal R⁰ K) ↔ x ∈ v.adicCompletionIntegers K := by
  rw [mem_localIdeal_iff (one_ne_zero (α := FractionalIdeal R⁰ K)), FractionalIdeal.count_one, mem_adicCompletionIntegers]
  simp

@[simp] theorem adele_mul_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

@[simp] theorem adele_add_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a + b) v = a v + b v := rfl

@[simp] theorem adele_sub_apply (a b : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (a - b) v = a v - b v := rfl

@[simp] theorem adele_one_apply (v : HeightOneSpectrum R) : (1 : 𝔸ᶠ[R, K]) v = 1 := rfl

@[simp] theorem adele_zero_apply (v : HeightOneSpectrum R) : (0 : 𝔸ᶠ[R, K]) v = 0 := rfl

theorem adele_algebraMap_apply (x : K) (v : HeightOneSpectrum R) :
    algebraMap K 𝔸ᶠ[R, K] x v = algebraMap K (v.adicCompletion K) x := rfl

theorem adele_smul_apply (r : R) (a : 𝔸ᶠ[R, K]) (v : HeightOneSpectrum R) :
    (r • a) v = algebraMap K (v.adicCompletion K) (algebraMap R K r) * a v := by
  rw [Algebra.smul_def]; rfl

def adelicIdeal (I : FractionalIdeal R⁰ K) : Submodule R 𝔸ᶠ[R, K] where
  carrier := {a | ∀ v, a v ∈ localIdeal v I}
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  smul_mem' r a ha v := by
    rw [adele_smul_apply]
    exact (localIdeal v I).smul_mem (algebraMap R (v.adicCompletionIntegers K) r) (ha v)

theorem mem_adelicIdeal {I : FractionalIdeal R⁰ K} {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal I ↔ ∀ v, a v ∈ localIdeal v I := Iff.rfl

theorem mem_adelicIdeal_iff {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal I ↔ ∀ v, Valued.v (a v) ≤ exp (-FractionalIdeal.count K v I) := by
  simp_rw [mem_adelicIdeal, mem_localIdeal_iff hI]

theorem algebraMap_mem_adelicIdeal {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal I ↔ x ∈ I := by
  simp_rw [mem_adelicIdeal_iff hI, mem_iff_valuation_le hI, adele_algebraMap_apply,
    valued_algebraMap]

theorem idele_apply_mul_inv (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    (t : 𝔸ᶠ[R, K]) v * ((t⁻¹ : 𝔸ᶠ[R, K]ˣ) : 𝔸ᶠ[R, K]) v = 1 := by
  rw [← adele_mul_apply, Units.mul_inv, adele_one_apply]

theorem idele_apply_ne_zero (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    (t : 𝔸ᶠ[R, K]) v ≠ 0 := left_ne_zero_of_mul_eq_one (idele_apply_mul_inv t v)

def ord_vw (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) : ℤ := -log (Valued.v ((t : 𝔸ᶠ[R, K]) v))

theorem valued_idele (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    Valued.v ((t : 𝔸ᶠ[R, K]) v) = exp (-ord_vw t v) := by
  rw [ord_vw, neg_neg, exp_log]
  simpa using idele_apply_ne_zero t v

theorem ord_vw_mul (t s : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    ord_vw (t * s) v = ord_vw t v + ord_vw s v := by
  have := valued_idele (t * s) v
  rw [Units.val_mul, adele_mul_apply, map_mul, valued_idele, valued_idele, ← exp_add,
    exp_inj] at this
  omega

theorem ord_vw_one (v : HeightOneSpectrum R) : ord_vw (1 : 𝔸ᶠ[R, K]ˣ) v = 0 := by
  have := ord_vw_mul (1 : 𝔸ᶠ[R, K]ˣ) 1 v
  rw [one_mul] at this
  omega

theorem ord_vw_inv (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) : ord_vw t⁻¹ v = -ord_vw t v := by
  have := ord_vw_mul t t⁻¹ v
  rw [mul_inv_cancel, ord_vw_one] at this
  omega

theorem ord_vw_eventually_zero (t : 𝔸ᶠ[R, K]ˣ) : ∀ᶠ v in Filter.cofinite, ord_vw t v = 0 := by
  filter_upwards [(FiniteAdeleRing.isUnit_iff.1 t.isUnit).2] with v hv
  simp [ord_vw, hv]

def idealOf (t : 𝔸ᶠ[R, K]ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ord_vw t v

theorem idealOf_ne_zero (t : 𝔸ᶠ[R, K]ˣ) : idealOf t ≠ 0 := by
  refine finprod_induction (fun L : FractionalIdeal R⁰ K => L ≠ 0) one_ne_zero
    (fun _ _ => mul_ne_zero) fun v => zpow_ne_zero _ ?_
  simpa using v.ne_bot

theorem count_idealOf (t : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (idealOf t) = ord_vw t v :=
  FractionalIdeal.count_finprod K v _ (ord_vw_eventually_zero t)

theorem idealOf_one : idealOf (1 : 𝔸ᶠ[R, K]ˣ) = 1 :=
  eq_of_count_eq (idealOf_ne_zero _) one_ne_zero fun v => by
    rw [count_idealOf, ord_vw_one, FractionalIdeal.count_one]

theorem idealOf_mul (t s : 𝔸ᶠ[R, K]ˣ) : idealOf (t * s) = idealOf t * idealOf s :=
  eq_of_count_eq (idealOf_ne_zero _) (mul_ne_zero (idealOf_ne_zero _) (idealOf_ne_zero _))
    fun v => by
      rw [FractionalIdeal.count_mul K v (idealOf_ne_zero _) (idealOf_ne_zero _), count_idealOf,
        count_idealOf, count_idealOf, ord_vw_mul]

theorem idealOf_inv (t : 𝔸ᶠ[R, K]ˣ) : idealOf t⁻¹ = (idealOf t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← idealOf_mul, inv_mul_cancel, idealOf_one])

scoped instance mulActionFractionalIdeal : MulAction 𝔸ᶠ[R, K]ˣ (FractionalIdeal R⁰ K) where
  smul t I := idealOf t * I
  one_smul I := by change idealOf 1 * I = I; rw [idealOf_one, one_mul]
  mul_smul t s I := by
    change idealOf (t * s) * I = idealOf t * (idealOf s * I); rw [idealOf_mul, mul_assoc]

theorem smul_def (t : 𝔸ᶠ[R, K]ˣ) (I : FractionalIdeal R⁰ K) : t • I = idealOf t * I := rfl

theorem smul_one_eq (t : 𝔸ᶠ[R, K]ˣ) : t • (1 : FractionalIdeal R⁰ K) = idealOf t := mul_one _

theorem smul_mul (t : 𝔸ᶠ[R, K]ˣ) (I J : FractionalIdeal R⁰ K) : t • (I * J) = (t • I) * J :=
  (mul_assoc _ _ _).symm

theorem smul_ne_zero (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) : t • I ≠ 0 :=
  mul_ne_zero (idealOf_ne_zero t) hI

theorem smul_le_smul (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : I ≤ J) :
    t • I ≤ t • J := by
  rw [smul_def, smul_def]; gcongr

theorem count_smul (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (t • I) = ord_vw t v + FractionalIdeal.count K v I := by
  rw [smul_def, FractionalIdeal.count_mul K v (idealOf_ne_zero _) hI, count_idealOf]

theorem mul_mem_localIdeal_smul (t : 𝔸ᶠ[R, K]ˣ) (I : FractionalIdeal R⁰ K)
    (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (t : 𝔸ᶠ[R, K]) v * x ∈ localIdeal v (t • I) ↔ x ∈ localIdeal v I := by
  rcases eq_or_ne I 0 with rfl | hI
  · simp [smul_def, localIdeal_zero, idele_apply_ne_zero]
  rw [mem_localIdeal_iff hI, mem_localIdeal_iff (smul_ne_zero t hI), count_smul t hI, map_mul,
    valued_idele, neg_add, exp_add, mul_le_mul_iff_right₀ (zero_lt_iff.2 exp_ne_zero)]

theorem mul_mem_adelicIdeal_smul (t : 𝔸ᶠ[R, K]ˣ) (I : FractionalIdeal R⁰ K) (a : 𝔸ᶠ[R, K]) :
    (t : 𝔸ᶠ[R, K]) * a ∈ adelicIdeal (t • I) ↔ a ∈ adelicIdeal I := by
  simp_rw [mem_adelicIdeal, adele_mul_apply, mul_mem_localIdeal_smul]

theorem mem_smul_iff (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ t • I ↔ ∃ a ∈ adelicIdeal I, (t : 𝔸ᶠ[R, K]) * a = algebraMap K 𝔸ᶠ[R, K] x := by
  rw [← algebraMap_mem_adelicIdeal (smul_ne_zero t hI)]
  constructor
  · intro h
    refine ⟨(t⁻¹ : 𝔸ᶠ[R, K]ˣ) * algebraMap K 𝔸ᶠ[R, K] x, ?_, by simp⟩
    rw [← mul_mem_adelicIdeal_smul t]
    simpa using h
  · rintro ⟨a, ha, h⟩
    rw [← h, mul_mem_adelicIdeal_smul]
    exact ha

theorem idealOf_unitEmbedding (x : Kˣ) :
    idealOf (FiniteAdeleRing.unitEmbedding R K x) = FractionalIdeal.spanSingleton R⁰ (x : K) :=
  eq_of_count_eq (idealOf_ne_zero _) (FractionalIdeal.spanSingleton_ne_zero_iff.2 x.ne_zero)
    fun v => by
      have := valued_idele (FiniteAdeleRing.unitEmbedding R K x) v
      rw [FiniteAdeleRing.unitEmbedding_apply, adele_algebraMap_apply, valued_algebraMap,
        valuation_eq_exp_neg_count v x.ne_zero, exp_inj] at this
      rw [count_idealOf]
      omega

theorem smul_eq_self_iff (t : 𝔸ᶠ[R, K]ˣ) {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    t • I = I ↔ ∀ v, Valued.v ((t : 𝔸ᶠ[R, K]) v) = 1 := by
  constructor
  · intro h v
    have := count_smul t hI v
    rw [h] at this
    rw [valued_idele, show ord_vw t v = 0 by omega]
    simp
  · intro h
    refine eq_of_count_eq (smul_ne_zero t hI) hI fun v => ?_
    rw [count_smul t hI, ord_vw, h v]
    simp

theorem exists_idealOf_eq {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∃ t : 𝔸ᶠ[R, K]ˣ, idealOf t = I := by
  choose f hf using fun v : HeightOneSpectrum R =>
    valuedAdicCompletion_surjective K v (exp (-FractionalIdeal.count K v I))
  have h1 : ∀ᶠ v in Filter.cofinite, Valued.v (f v) = 1 := by
    filter_upwards [FractionalIdeal.finite_factors I] with v hv
    rw [hf, hv]; simp
  let a : 𝔸ᶠ[R, K] := ⟨f, h1.mono fun v hv => hv.le⟩
  have ha : IsUnit a := by
    refine FiniteAdeleRing.isUnit_iff.2 ⟨fun v h => ?_, h1⟩
    have := hf v
    change f v = 0 at h
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  refine ⟨ha.unit, eq_of_count_eq (idealOf_ne_zero _) hI fun v => ?_⟩
  have := valued_idele ha.unit v
  rw [count_idealOf]
  change Valued.v (f v) = _ at this
  rw [hf, exp_inj] at this
  omega

theorem exists_smul_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    ∃ t : 𝔸ᶠ[R, K]ˣ, J = t • I := by
  obtain ⟨t, ht⟩ := exists_idealOf_eq (mul_ne_zero hJ (inv_ne_zero hI))
  exact ⟨t, by rw [smul_def, ht, mul_assoc, inv_mul_cancel₀ hI, mul_one]⟩

theorem setOf_valued_le_eq (v : HeightOneSpectrum R) (n : ℤ) :
    ∃ c : v.adicCompletion K, Valued.v.restrict c ≠ 0 ∧
      {y : v.adicCompletion K | Valued.v y ≤ exp n} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
  obtain ⟨c, hc⟩ := valuedAdicCompletion_surjective K v (exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact exp_ne_zero hc.symm
  refine ⟨c, by simp [hc0], ?_⟩
  ext y
  simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hc]

theorem isOpen_valued_le (v : HeightOneSpectrum R) (n : ℤ) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ exp n} := by
  obtain ⟨c, hc, h⟩ := setOf_valued_le_eq (K := K) v n
  rw [h]; exact Valued.isOpen_closedBall _ hc

theorem isClosed_valued_le (v : HeightOneSpectrum R) (n : ℤ) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ exp n} := by
  obtain ⟨c, hc, h⟩ := setOf_valued_le_eq (K := K) v n
  rw [h]; exact Valued.isClosed_closedBall _ _

theorem exists_exp_neg_lt {γ : ℤᵐ⁰} (hγ : γ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < γ := by
  refine ⟨(log γ).natAbs + 1, ?_⟩
  conv_rhs => rw [← exp_log hγ]
  rw [exp_lt_exp]
  omega

theorem exists_limit (v : HeightOneSpectrum R) (u : ℕ → v.adicCompletion K)
    (hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ))) :
    ∃ t : v.adicCompletion K, ∀ n : ℕ, Valued.v (t - u n) ≤ exp (-(n : ℤ)) := by
  have hc : CauchySeq u := by
    rw [(Valued.hasBasis_uniformity (v.adicCompletion K) ℤᵐ⁰).cauchySeq_iff']
    intro γ _
    obtain ⟨n, hn⟩ := exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun m hm => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    rw [Valuation.map_sub_swap]
    exact (hu m n hm).trans_lt hn
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨t, fun n => ?_⟩
  refine (isClosed_valued_le (K := K) v (-(n : ℤ))).mem_of_tendsto (ht.sub_const (u n)) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm using hu m n hm

theorem exists_valued_sub_le (v : HeightOneSpectrum R) {a : v.adicCompletion K}
    (ha : Valued.v a ≤ 1) (n : ℕ) :
    ∃ r : R, Valued.v (a - algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤
      exp (-(n : ℤ)) := by
  have ho : IsOpen {y : v.adicCompletion K | Valued.v (a - y) ≤ exp (-(n : ℤ))} :=
    (isOpen_valued_le (K := K) v (-(n : ℤ))).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (denseRange_algebraMap K v).exists_mem_open ho ⟨a, by simp⟩
  have hx : Valued.v (a - algebraMap K (v.adicCompletion K) x) ≤ exp (-(n : ℤ)) := hx
  have h1 : exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by rw [← exp_zero, exp_le_exp]; omega
  have hx1 : v.valuation K x ≤ 1 := by
    rw [← valued_algebraMap, ← sub_sub_cancel a (algebraMap K (v.adicCompletion K) x)]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (hx.trans h1))
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hx1 (Units.mk0 _ (exp_ne_zero (a := -(n : ℤ))))
  refine ⟨r, ?_⟩
  rw [← valued_algebraMap, map_sub, Valuation.map_sub_swap] at hr
  rw [← sub_add_sub_cancel a (algebraMap K (v.adicCompletion K) x)]
  exact (Valuation.map_add _ _ _).trans (max_le hx hr.le)

theorem exists_sub_mem_adelicIdeal_of_integral {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    {a : 𝔸ᶠ[R, K]} (ha : ∀ v, Valued.v (a v) ≤ 1) :
    ∃ r : R, a - algebraMap K 𝔸ᶠ[R, K] (algebraMap R K r) ∈ adelicIdeal I := by
  classical
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)
  let e : HeightOneSpectrum R → ℕ := fun v => (FractionalIdeal.count K v I).toNat
  choose x hx using fun v => exists_valued_sub_le v (ha v) (e v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun v => v.asIdeal) e (fun v _ => v.prime)
    (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => x v)
  refine ⟨r, (mem_adelicIdeal_iff hI).2 fun v => ?_⟩
  rw [adele_sub_apply, adele_algebraMap_apply]
  have hr1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1 := by
    rw [valued_algebraMap]; exact v.valuation_le_one r
  by_cases hv : v ∈ hfin.toFinset
  · have h2 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.valuation_of_algebraMap (K := K)] at h2
    change v.valuation K (algebraMap R K (r - x v)) ≤ _ at h2
    rw [← valued_algebraMap, map_sub, map_sub, Valuation.map_sub_swap] at h2
    rw [← sub_add_sub_cancel (a v) (algebraMap K (v.adicCompletion K) (algebraMap R K (x v)))]
    refine ((Valuation.map_add _ _ _).trans (max_le (hx v) h2)).trans ?_
    rw [exp_le_exp]
    simp only [e]
    omega
  · have : FractionalIdeal.count K v I = 0 := by simpa using hv
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le (ha v) hr1)

theorem exists_mul_integral (a : 𝔸ᶠ[R, K]) :
    ∃ b : R, b ≠ 0 ∧ ∀ v, Valued.v ((algebraMap K 𝔸ᶠ[R, K] (algebraMap R K b) * a) v) ≤ 1 := by
  classical
  have hfin := Filter.eventually_cofinite.1 a.2
  choose b hb0 hb using fun v : HeightOneSpectrum R =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  have hle : ∀ (v : HeightOneSpectrum R) (r : R),
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1 := fun v r => by
    rw [valued_algebraMap]; exact v.valuation_le_one r
  refine ⟨∏ v ∈ hfin.toFinset, b v,
    Finset.prod_ne_zero_iff.2 fun v _ => nonZeroDivisors.ne_zero (hb0 v), fun v => ?_⟩
  rw [adele_mul_apply, adele_algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.prod_erase_mul _ _ hv, map_mul (algebraMap R K),
      map_mul (algebraMap K (v.adicCompletion K)), mul_assoc, map_mul]
    refine mul_le_one' (hle v _) ?_
    rw [mul_comm]
    exact hb v
  · have : a.1 v ∈ v.adicCompletionIntegers K := by simpa using hv
    rw [map_mul]
    exact mul_le_one' (hle v _) (show Valued.v (a v) ≤ 1 from this)

theorem exists_sub_mem_adelicIdeal {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (a : 𝔸ᶠ[R, K]) :
    ∃ x : K, a - algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal I := by
  obtain ⟨b, hb0, hb⟩ := exists_mul_integral a
  have hb1 : algebraMap R K b ≠ 0 := by simpa using hb0
  let t := FiniteAdeleRing.unitEmbedding R K (Units.mk0 _ hb1)
  obtain ⟨r, hr⟩ := exists_sub_mem_adelicIdeal_of_integral (smul_ne_zero t hI) hb
  refine ⟨algebraMap R K r / algebraMap R K b, ?_⟩
  rw [← mul_mem_adelicIdeal_smul t]
  convert hr using 1
  simp only [t, FiniteAdeleRing.unitEmbedding_apply, Units.val_mk0]
  rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hb1]

def quotEquivAdelic {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (K ⧸ (I : Submodule R K)) ≃ₗ[R] (𝔸ᶠ[R, K] ⧸ adelicIdeal I) :=
  LinearEquiv.ofBijective
    (Submodule.mapQ (I : Submodule R K) (adelicIdeal I)
      ((Algebra.linearMap K 𝔸ᶠ[R, K]).restrictScalars R)
      fun x hx => (algebraMap_mem_adelicIdeal hI x).2 hx) <| by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.Quotient.mk_eq_zero]
      exact (algebraMap_mem_adelicIdeal hI x).1 ((Submodule.Quotient.mk_eq_zero _).1 hq)
    · intro q
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal hI a
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      exact ((Submodule.Quotient.eq _).2 hx).symm

@[simp] theorem quotEquivAdelic_mk {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    quotEquivAdelic hI (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (algebraMap K 𝔸ᶠ[R, K] x) := rfl

def adelicMulEquiv (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : J = t • I) :
    (𝔸ᶠ[R, K] ⧸ adelicIdeal I) ≃ₗ[R] (𝔸ᶠ[R, K] ⧸ adelicIdeal J) :=
  Submodule.Quotient.equiv _ _ (Units.mulLeftLinearEquiv R 𝔸ᶠ[R, K] t) <| by
    subst h
    ext a
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (mul_mem_adelicIdeal_smul t I c).2 hc
    · intro ha
      refine ⟨(t⁻¹ : 𝔸ᶠ[R, K]ˣ) * a, ?_, by simp⟩
      rw [← mul_mem_adelicIdeal_smul t]
      simpa using ha

@[simp] theorem adelicMulEquiv_mk (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : J = t • I)
    (a : 𝔸ᶠ[R, K]) :
    adelicMulEquiv t h (Submodule.Quotient.mk a) = Submodule.Quotient.mk ((t : 𝔸ᶠ[R, K]) * a) :=
  rfl

def mulEquiv (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (h : J = t • I) :
    (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K)) :=
  (quotEquivAdelic hI).trans <| (adelicMulEquiv t h).trans
    (quotEquivAdelic (h ▸ smul_ne_zero t hI)).symm

theorem quotEquivAdelic_mulEquiv (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (hJ : J ≠ 0) (h : J = t • I) (q : K ⧸ (I : Submodule R K)) :
    quotEquivAdelic hJ (mulEquiv t hI h q) = adelicMulEquiv t h (quotEquivAdelic hI q) := by
  simp [mulEquiv]

theorem mulEquiv_mk_eq_mk_iff_adelic (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (x y : K) :
    mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      (t : 𝔸ᶠ[R, K]) * algebraMap K _ x - algebraMap K _ y ∈ adelicIdeal J := by
  have hJ : J ≠ 0 := h ▸ smul_ne_zero t hI
  rw [← (quotEquivAdelic hJ).injective.eq_iff, quotEquivAdelic_mulEquiv, quotEquivAdelic_mk,
    quotEquivAdelic_mk, adelicMulEquiv_mk, Submodule.Quotient.eq]

theorem mulEquiv_mk_eq_mk_iff (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (x y : K) :
    mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      ∀ v : HeightOneSpectrum R, (t : 𝔸ᶠ[R, K]) v * algebraMap K (v.adicCompletion K) x -
        algebraMap K (v.adicCompletion K) y ∈ localIdeal v J :=
  mulEquiv_mk_eq_mk_iff_adelic t hI h x y

theorem mulEquiv_one {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (h : I = (1 : 𝔸ᶠ[R, K]ˣ) • I) :
    mulEquiv 1 hI h = LinearEquiv.refl R _ := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearEquiv.refl_apply, mulEquiv_mk_eq_mk_iff_adelic]
  simp

theorem mulEquiv_mul (t s : 𝔸ᶠ[R, K]ˣ) {I J L : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : J = s • I) (h' : L = t • J) (h'' : L = (t * s) • I) :
    mulEquiv (t * s) hI h'' = (mulEquiv s hI h).trans (mulEquiv t hJ h') := by
  have hL : L ≠ 0 := h' ▸ smul_ne_zero t hJ
  refine LinearEquiv.ext fun q => (quotEquivAdelic hL).injective ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearEquiv.trans_apply, quotEquivAdelic_mulEquiv, quotEquivAdelic_mulEquiv,
    quotEquivAdelic_mulEquiv]
  simp [mul_assoc]

theorem mulEquiv_unitEmbedding_mk (c : Kˣ) {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = FiniteAdeleRing.unitEmbedding R K c • I) (x : K) :
    mulEquiv (FiniteAdeleRing.unitEmbedding R K c) hI h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((c : K) * x) := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  simp

theorem mulEquiv_mk_mul (t : 𝔸ᶠ[R, K]ˣ) {I J I' J' : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (hI' : I' ≠ 0) (h : J = t • I) (h' : J' = t • I') {c : K} (hc : ∀ z ∈ I, c * z ∈ I') {x y : K}
    (hxy : mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) :
    mulEquiv t hI' h' (Submodule.Quotient.mk (c * x)) = Submodule.Quotient.mk (c * y) := by
  rw [mulEquiv_mk_eq_mk_iff] at hxy ⊢
  intro v
  subst h h'
  have key : ∀ z ∈ localIdeal v I, algebraMap K (v.adicCompletion K) c * z ∈ localIdeal v I' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨z, hz, rfl⟩ := hz
      exact Submodule.subset_span ⟨c * z, hc z hz, map_mul _ _ _⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul a b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  have ht := idele_apply_ne_zero t v
  have h1 := hxy v
  rw [← mul_div_cancel₀ (_ - _) ht, mul_mem_localIdeal_smul] at h1 ⊢
  convert key _ h1 using 1
  rw [map_mul, map_mul]
  ring

theorem mulEquiv_mem_iff (t : 𝔸ᶠ[R, K]ˣ) {I J I' : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (hle : I ≤ I') {x y : K}
    (hxy : mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) :
    y ∈ t • I' ↔ x ∈ I' := by
  have hI' : I' ≠ 0 := fun h0 => hI (le_antisymm (h0 ▸ hle) (FractionalIdeal.zero_le I))
  have := mulEquiv_mk_mul t hI hI' h rfl (c := 1) (fun z hz => by simpa using hle hz) hxy
  rw [one_mul, one_mul] at this
  rw [← FractionalIdeal.mem_coe, ← FractionalIdeal.mem_coe, ← Submodule.Quotient.mk_eq_zero,
    ← Submodule.Quotient.mk_eq_zero, ← this, LinearEquiv.map_eq_zero_iff]

theorem mem_adelicIdeal_one_iff {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) ↔ ∀ v, Valued.v (a v) ≤ 1 := by
  simp_rw [mem_adelicIdeal, mem_localIdeal_one_iff, mem_adicCompletionIntegers]

theorem exists_adele_of_end_one
    (ψ : (𝔸ᶠ[R, K] ⧸ adelicIdeal (1 : FractionalIdeal R⁰ K)) →ₗ[R]
      (𝔸ᶠ[R, K] ⧸ adelicIdeal (1 : FractionalIdeal R⁰ K))) :
    ∃ t : 𝔸ᶠ[R, K], ∀ a, ψ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (t * a) := by
  choose y hy using fun b : R => Submodule.Quotient.mk_surjective _
    (ψ (Submodule.Quotient.mk (algebraMap K 𝔸ᶠ[R, K] (algebraMap R K b)⁻¹)))
  let ι : ∀ v : HeightOneSpectrum R, R → v.adicCompletion K :=
    fun v b => algebraMap K (v.adicCompletion K) (algebraMap R K b)
  have hsm : ∀ (r : R) (x : K), r • algebraMap K 𝔸ᶠ[R, K] x =
      algebraMap K 𝔸ᶠ[R, K] (algebraMap R K r * x) := fun r x => by
    rw [Algebra.smul_def, map_mul]; rfl

  have hint : ∀ b v, Valued.v (ι v b * y b v) ≤ 1 := by
    intro b v
    have : b • y b ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, hy, ← map_smul,
        ← Submodule.Quotient.mk_smul, hsm, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [algebraMap_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal R⁰ K))]
      rcases eq_or_ne (algebraMap R K b) 0 with h | h
      · simp [h, FractionalIdeal.zero_mem]
      · rw [mul_inv_cancel₀ h]; exact FractionalIdeal.one_mem_one _
    have := mem_adelicIdeal_one_iff.1 this v
    rwa [adele_smul_apply] at this

  have hcomp : ∀ b c, c ≠ 0 → ∀ v,
      Valued.v (ι v (b * c) * y (b * c) v - ι v b * y b v) ≤ Valued.v (ι v b) := by
    intro b c hc v
    have hc1 : algebraMap R K c ≠ 0 := by simpa using hc
    have : c • y (b * c) - y b ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul, hy, hy, ← map_smul,
        ← Submodule.Quotient.mk_smul, hsm, map_mul (algebraMap R K), mul_inv, mul_comm,
        mul_assoc, inv_mul_cancel₀ hc1, mul_one]
    have := mem_adelicIdeal_one_iff.1 this v
    rw [adele_sub_apply, adele_smul_apply] at this
    have h2 : ι v (b * c) * y (b * c) v - ι v b * y b v = ι v b * (ι v c * y (b * c) v - y b v) := by
      simp only [ι, map_mul]; ring
    rw [h2, map_mul]
    exact mul_le_of_le_one_right' this
  choose π hπ using fun v : HeightOneSpectrum R => v.valuation_exists_uniformizer' K
  have hπn : ∀ v (n : ℕ), Valued.v (ι v (π v ^ n)) = exp (-(n : ℤ)) := by
    intro v n
    have : v.valuation K (algebraMap R K (π v)) = exp (-1) := hπ v
    simp only [ι]
    rw [valued_algebraMap, map_pow, map_pow, this, ← exp_nsmul]
    simp
  have hπ0 : ∀ v (n : ℕ), π v ^ n ≠ 0 := by
    intro v n h
    have := hπn v n
    rw [h] at this
    simp only [ι, map_zero] at this
    exact exp_ne_zero this.symm
  have hlim : ∀ v, ∃ t : v.adicCompletion K, ∀ n : ℕ,
      Valued.v (t - ι v (π v ^ n) * y (π v ^ n) v) ≤ exp (-(n : ℤ)) := by
    intro v
    refine exists_limit v _ fun m n hnm => ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, ← hπn v n]
    exact hcomp _ _ (hπ0 v k) v
  choose t ht using hlim
  have htb : ∀ b, b ≠ 0 → ∀ v, Valued.v (t v - ι v b * y b v) ≤ Valued.v (ι v b) := by
    intro b hb v
    have hb0 : Valued.v (ι v b) ≠ 0 := by simpa [ι] using hb
    obtain ⟨n, hn⟩ := exists_exp_neg_lt hb0
    have h1 := (ht v n).trans hn.le
    have h2 := hcomp b (π v ^ n) (hπ0 v n) v
    have h3 := hcomp (π v ^ n) b hb v
    rw [hπn, mul_comm (π v ^ n) b, Valuation.map_sub_swap] at h3
    rw [← sub_add_sub_cancel (t v) (ι v (π v ^ n) * y (π v ^ n) v),
      ← sub_add_sub_cancel (ι v (π v ^ n) * y (π v ^ n) v)
        (ι v (b * π v ^ n) * y (b * π v ^ n) v)]
    exact (Valuation.map_add _ _ _).trans (max_le h1
      ((Valuation.map_add _ _ _).trans (max_le (h3.trans hn.le) h2)))
  have ht1 : ∀ v, Valued.v (t v) ≤ 1 := by
    intro v
    have h1 := ht v 0
    rw [← sub_add_cancel (t v) (ι v (π v ^ 0) * y (π v ^ 0) v)]
    exact (Valuation.map_add _ _ _).trans (max_le (by simpa using h1) (hint _ v))
  let T : 𝔸ᶠ[R, K] := ⟨t, Filter.Eventually.of_forall fun v => ht1 v⟩
  have hT : ∀ v, T v = t v := fun _ => rfl
  refine ⟨T, fun a => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal R⁰ K)) a
  obtain ⟨r, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [(Submodule.Quotient.eq _).2 hx, div_eq_mul_inv, ← hsm, Submodule.Quotient.mk_smul, map_smul,
    ← hy, ← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, mem_adelicIdeal_one_iff]
  intro v
  have hx' := mem_adelicIdeal_one_iff.1 hx v
  rw [adele_sub_apply, adele_algebraMap_apply, map_div₀] at hx'
  have hb1 : ι v b ≠ 0 := by simpa [ι] using hb0
  have hb2 : Valued.v (ι v b) ≠ 0 := by simpa using hb1
  have h2 : (T * a - r • y b) v =
      t v * (a v - ι v r / ι v b) + ι v r * ((t v - ι v b * y b v) / ι v b) := by
    rw [adele_sub_apply, adele_mul_apply, adele_smul_apply, hT]
    change t v * a v - ι v r * y b v = _
    field_simp
    ring
  rw [h2]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (ht1 v) hx'
  · rw [map_mul, map_div₀]
    refine mul_le_one' ?_ ((div_le_one₀ (zero_lt_iff.2 hb2)).2 (htb b hb0 v))
    simp only [ι]
    rw [valued_algebraMap]; exact v.valuation_le_one r

theorem exists_adele_of_linearMap {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (ψ : (𝔸ᶠ[R, K] ⧸ adelicIdeal I) →ₗ[R] (𝔸ᶠ[R, K] ⧸ adelicIdeal J)) :
    ∃ t : 𝔸ᶠ[R, K], ∀ a, ψ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (t * a) := by
  obtain ⟨s, hs⟩ := exists_smul_eq (one_ne_zero (α := FractionalIdeal R⁰ K)) hI
  obtain ⟨u, hu⟩ := exists_smul_eq (one_ne_zero (α := FractionalIdeal R⁰ K)) hJ
  obtain ⟨t, ht⟩ := exists_adele_of_end_one
    ((adelicMulEquiv u hu).symm.toLinearMap ∘ₗ ψ ∘ₗ (adelicMulEquiv s hs).toLinearMap)
  refine ⟨u * t * (s⁻¹ : 𝔸ᶠ[R, K]ˣ), fun a => ?_⟩
  have := ht ((s⁻¹ : 𝔸ᶠ[R, K]ˣ) * a)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, adelicMulEquiv_mk,
    LinearEquiv.symm_apply_eq, Units.mul_inv_cancel_left] at this
  rw [this, mul_assoc, mul_assoc]

theorem eq_zero_of_forall_mul_mem {J : FractionalIdeal R⁰ K} (hJ : J ≠ 0) {t : 𝔸ᶠ[R, K]}
    (h : ∀ x : K, t * algebraMap K 𝔸ᶠ[R, K] x ∈ adelicIdeal J) : t = 0 := by
  ext1 v
  by_contra hv
  have hv' : Valued.v (t v) ≠ 0 := by simpa using hv
  obtain ⟨x, hx⟩ := v.valuation_surjective K
    (exp (1 - FractionalIdeal.count K v J - log (Valued.v (t v))))
  have := (mem_adelicIdeal_iff hJ).1 (h x) v
  rw [adele_mul_apply, adele_algebraMap_apply, map_mul, valued_algebraMap, hx,
    ← exp_log hv', ← exp_add, exp_le_exp, log_exp] at this
  omega

theorem existsUnique_adele_of_linearMap {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) →ₗ[R] (K ⧸ (J : Submodule R K))) :
    ∃! t : 𝔸ᶠ[R, K], ∀ x : K, quotEquivAdelic hJ (φ (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (t * algebraMap K 𝔸ᶠ[R, K] x) := by
  obtain ⟨t, ht⟩ := exists_adele_of_linearMap hI hJ
    ((quotEquivAdelic hJ).toLinearMap ∘ₗ φ ∘ₗ (quotEquivAdelic hI).symm.toLinearMap)
  have ht' : ∀ x : K, quotEquivAdelic hJ (φ (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (t * algebraMap K 𝔸ᶠ[R, K] x) := fun x => by
    rw [← ht, ← quotEquivAdelic_mk hI]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  refine ⟨t, ht', fun s hs => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mul_mem hJ fun x => ?_
  rw [sub_mul, ← Submodule.Quotient.eq, ← hs, ← ht']

theorem mulEquiv_injective {t s : 𝔸ᶠ[R, K]ˣ} {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (h' : J = s • I) (e : mulEquiv t hI h = mulEquiv s hI h') : t = s := by
  have hJ : J ≠ 0 := h ▸ smul_ne_zero t hI
  refine Units.ext ((existsUnique_adele_of_linearMap hI hJ (mulEquiv t hI h).toLinearMap).unique
    (fun x => ?_) fun x => ?_)
  · simp [quotEquivAdelic_mulEquiv]
  · simp [e, quotEquivAdelic_mulEquiv]

theorem ne_zero_of_linearEquiv {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K))) : J ≠ 0 := by
  rintro rfl
  obtain ⟨q, hq⟩ := φ.surjective (Submodule.Quotient.mk 1)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨c, hc0, hc⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  obtain ⟨r, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap R K b ≠ 0 := by simpa using hb0
  have h0 : (b * c) • (Submodule.Quotient.mk (algebraMap R K r / algebraMap R K b) :
      K ⧸ (I : Submodule R K)) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    convert (I : Submodule R K).smul_mem r hc using 1
    simp only [Algebra.smul_def, map_mul]
    field_simp
  have h1 := congrArg φ h0
  rw [map_smul, hq, map_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_zero_iff] at h1
  simp [Algebra.smul_def, hb0, hc0] at h1

theorem existsUnique_mulEquiv {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (φ : (K ⧸ (I : Submodule R K)) ≃ₗ[R] (K ⧸ (J : Submodule R K))) :
    ∃! t : 𝔸ᶠ[R, K]ˣ, ∃ h : J = t • I, φ = mulEquiv t hI h := by
  have hJ : J ≠ 0 := ne_zero_of_linearEquiv hI φ
  let ψ := (quotEquivAdelic hI).symm.trans (φ.trans (quotEquivAdelic hJ))
  obtain ⟨t, ht⟩ := exists_adele_of_linearMap hI hJ ψ.toLinearMap
  obtain ⟨s, hs⟩ := exists_adele_of_linearMap hJ hI ψ.symm.toLinearMap
  simp only [LinearEquiv.coe_coe] at ht hs
  have hst : s * t = 1 := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mul_mem hI fun x => ?_
    rw [sub_mul, ← Submodule.Quotient.eq, mul_assoc, ← hs, ← ht, LinearEquiv.symm_apply_apply,
      one_mul]
  let u : 𝔸ᶠ[R, K]ˣ := ⟨t, s, by rw [mul_comm, hst], hst⟩
  have hu : J = u • I := by
    ext x
    rw [← algebraMap_mem_adelicIdeal hJ, ← algebraMap_mem_adelicIdeal (smul_ne_zero u hI),
      ← Units.mul_inv_cancel_left u (algebraMap K 𝔸ᶠ[R, K] x), mul_mem_adelicIdeal_smul,
      ← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero]
    exact (ht _) ▸ ψ.map_eq_zero_iff
  have hφ : φ = mulEquiv u hI hu := by
    refine LinearEquiv.ext fun q => (quotEquivAdelic hJ).injective ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [quotEquivAdelic_mulEquiv, quotEquivAdelic_mk, adelicMulEquiv_mk]
    refine Eq.trans ?_ (ht _)
    rw [← quotEquivAdelic_mk hI]
    simp only [ψ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  refine ⟨u, ⟨hu, hφ⟩, ?_⟩
  rintro u' ⟨hu', hφ'⟩
  exact mulEquiv_injective hI hu' hu (hφ'.symm.trans hφ)

end GlobalTheory.Idele

namespace GlobalTheory

open NumberField GlobalTheory.Idele

theorem existsUnique_idele_of_linearEquiv_quotient {K : Type*} [Field K] [NumberField K]
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
    (φ : (K ⧸ ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) →ₗ[𝓞 K]
      (K ⧸ (𝔞 : Submodule (𝓞 K) K))) (hφ : Function.Bijective φ) :
    ∃! t : (FiniteAdeleRing (𝓞 K) K)ˣ, ∃ h : 𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K),
      ∀ q, φ q = mulEquiv t⁻¹ one_ne_zero h q := by
  obtain ⟨t, ⟨h, ht⟩, huniq⟩ :=
    existsUnique_mulEquiv (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)) (LinearEquiv.ofBijective φ hφ)
  refine ⟨t⁻¹, ?_, ?_⟩
  · simp only [inv_inv]
    exact ⟨h, fun q => LinearEquiv.congr_fun ht q⟩
  · rintro s ⟨h', hs⟩
    rw [← huniq s⁻¹ ⟨h', LinearEquiv.ext hs⟩, inv_inv]

theorem existsUnique_idele_of_linearEquiv_quotient_local {K : Type*} [Field K] [NumberField K]
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
    (φ : (K ⧸ ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) →ₗ[𝓞 K]
      (K ⧸ (𝔞 : Submodule (𝓞 K) K))) (hφ : Function.Bijective φ) :
    ∃! t : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (∀ x : K, x ∈ 𝔞 ↔ ∀ v, (t : FiniteAdeleRing (𝓞 K) K) v * algebraMap K (v.adicCompletion K) x
        ∈ v.adicCompletionIntegers K) ∧
      ∀ x y : K, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
        ∀ v, ((t⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v *
          algebraMap K (v.adicCompletion K) x - algebraMap K (v.adicCompletion K) y ∈
            localIdeal v 𝔞 := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  have key : ∀ (t : (FiniteAdeleRing (𝓞 K) K)ˣ) (x : K),
      x ∈ t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
        ∀ v, (t : FiniteAdeleRing (𝓞 K) K) v * algebraMap K (v.adicCompletion K) x
          ∈ v.adicCompletionIntegers K := by
    intro t x
    rw [← algebraMap_mem_adelicIdeal (Idele.smul_ne_zero _ h1), ← mul_mem_adelicIdeal_smul t,
      smul_inv_smul, mem_adelicIdeal]
    simp_rw [mem_localIdeal_one_iff]
    rfl
  obtain ⟨t, ⟨h, ht⟩, huniq⟩ := existsUnique_idele_of_linearEquiv_quotient 𝔞 φ hφ
  refine ⟨t, ⟨fun x => by rw [← key, ← h], fun x y => by rw [ht, mulEquiv_mk_eq_mk_iff]⟩, ?_⟩
  rintro s ⟨hs, hs'⟩
  have h' : 𝔞 = s⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    ext x; rw [hs, key]
  refine huniq s ⟨h', fun q => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk x))
  rw [← hy, eq_comm, mulEquiv_mk_eq_mk_iff]
  exact (hs' x y).1 hy.symm

end GlobalTheory
