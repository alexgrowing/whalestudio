import Mathlib
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
  MeasureTheory WithZero
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem count_coeIdeal_eq_multiplicity (v : HeightOneSpectrum (𝓞 K)) {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) :
    FractionalIdeal.count K v (𝔪 : FractionalIdeal (𝓞 K)⁰ K) = multiplicity v.asIdeal 𝔪 := by
  have h0 : 𝔪 ≠ 0 := h𝔪
  rw [FractionalIdeal.count_coe K v h0, Ideal.count_associates_factors_eq h0 v.isPrime v.ne_bot,
    count_normalizedFactors_eq_multiplicity h𝔪]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem finite_setOf_dvd_conductor :
    {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ χ.conductor}.Finite :=
  Ideal.finite_factors χ.conductor_ne_bot

theorem localComponent_eq_one_of_mem_unitsLevel {v : HeightOneSpectrum (𝓞 K)}
    {u : (v.adicCompletion K)ˣ} (hu : u ∈ unitsLevel v (multiplicity v.asIdeal χ.conductor)) :
    χ.localComponent v u = 1 := by
  have h1 : finiteUnitsSingle v u ∈ idealLevel χ.conductor :=
    finiteUnitsSingle_mem_finiteLevel (n := fun w ↦ multiplicity w.asIdeal χ.conductor) hu
  have h2 := χ.map_idealLevel_conductor_le_ker (Subgroup.mem_map_of_mem ofFinite h1)
  rw [MonoidHom.mem_ker, ofFinite_finiteUnitsSingle] at h2
  exact h2

open Classical in

def finiteTest (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : ℂ :=
  if v.asIdeal ∣ χ.conductor then
    (if h : Valued.v x = 1 then
      (((χ.localComponent v (Units.mk0 x fun h0 ↦ by simp [h0] at h))⁻¹ : Circle) : ℂ) else 0)
  else if Valued.v x ≤ 1 then 1 else 0

def finiteTestFun (x : FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏ᶠ v, χ.finiteTest v (x v)

theorem finiteTest_eq_zero {v : HeightOneSpectrum (𝓞 K)} {x : v.adicCompletion K}
    (hx : 1 < Valued.v x) : χ.finiteTest v x = 0 := by
  unfold finiteTest
  split_ifs with h1 h2 h3
  · exact absurd h2 hx.ne'
  · rfl
  · exact absurd h3 (not_le.2 hx)
  · rfl

theorem finiteTest_eq_zero_of_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor)
    {x : v.adicCompletion K} (hx : Valued.v x ≠ 1) : χ.finiteTest v x = 0 := by
  unfold finiteTest
  rw [if_pos hv, dif_neg hx]

theorem finiteTest_eq_one {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor)
    {x : v.adicCompletion K} (hx : Valued.v x ≤ 1) : χ.finiteTest v x = 1 := by
  unfold finiteTest
  rw [if_neg hv, if_pos hx]

theorem finiteTest_of_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor)
    (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    χ.finiteTest v u = ((χ.localComponent v u : ℂ))⁻¹ := by
  unfold finiteTest
  rw [if_pos hv, dif_pos hu, Circle.coe_inv]
  congr 3
  exact Units.ext rfl

theorem finiteTest_add {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K)
    {h : v.adicCompletion K}
    (hh : Valued.v h ≤ exp (-(multiplicity v.asIdeal χ.conductor : ℤ))) :
    χ.finiteTest v (x + h) = χ.finiteTest v x := by
  by_cases hv : v.asIdeal ∣ χ.conductor
  · have hn : 1 ≤ multiplicity v.asIdeal χ.conductor := multiplicity_pos_of_dvd hv
    have hh1 : Valued.v h < 1 := by
      refine hh.trans_lt ?_
      rw [← exp_zero, exp_lt_exp]
      omega
    by_cases hx : Valued.v x = 1
    · have hxh : Valued.v (x + h) = 1 := by
        rw [Valuation.map_add_eq_of_lt_left _ (hx ▸ hh1), hx]
      have hx0 : x ≠ 0 := fun h0 ↦ by simp [h0] at hx
      have hxh0 : x + h ≠ 0 := fun h0 ↦ by simp [h0] at hxh
      have hu : Units.mk0 (1 + h / x) (by
          intro h0
          have : Valued.v (1 + h / x) = 1 := by
            rw [Valuation.map_add_eq_of_lt_left] <;> simp [map_div₀, hx, hh1]
          simp [h0] at this) ∈ unitsLevel v (multiplicity v.asIdeal χ.conductor) := by
        rw [mem_unitsLevel_of_one_le hn, Units.val_mk0, add_sub_cancel_left, map_div₀, hx,
          div_one]
        exact hh
      have hmk : Units.mk0 (x + h) hxh0 = Units.mk0 x hx0 * Units.mk0 (1 + h / x) (by
          intro h0
          have : Valued.v (1 + h / x) = 1 := by
            rw [Valuation.map_add_eq_of_lt_left] <;> simp [map_div₀, hx, hh1]
          simp [h0] at this) := by
        ext
        simp only [Units.val_mk0, Units.val_mul]
        field_simp
      have e1 := χ.finiteTest_of_dvd hv (Units.mk0 (x + h) hxh0) hxh
      have e2 := χ.finiteTest_of_dvd hv (Units.mk0 x hx0) hx
      simp only [Units.val_mk0] at e1 e2
      rw [e1, e2, hmk, map_mul, χ.localComponent_eq_one_of_mem_unitsLevel hu, mul_one]
    · have hxh : Valued.v (x + h) ≠ 1 := by
        intro hxh
        apply hx
        have : x = (x + h) + (-h) := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, hxh]; exact hh1),
          hxh]
      rw [χ.finiteTest_eq_zero_of_dvd hv hx, χ.finiteTest_eq_zero_of_dvd hv hxh]
  · rw [multiplicity_eq_zero.2 hv, Nat.cast_zero, neg_zero, exp_zero] at hh
    have hiff : Valued.v (x + h) ≤ 1 ↔ Valued.v x ≤ 1 := by
      constructor
      · intro hxh
        have : x = (x + h) + (-h) := by ring
        rw [this]
        exact (Valuation.map_add _ _ _).trans (max_le hxh (by rw [Valuation.map_neg]; exact hh))
      · intro hx
        exact (Valuation.map_add _ _ _).trans (max_le hx hh)
    unfold finiteTest
    simp only [if_neg hv, hiff]

theorem hasFiniteMulSupport_finiteTest (x : FiniteAdeleRing (𝓞 K) K) :
    Function.HasFiniteMulSupport fun v ↦ χ.finiteTest v (x v) := by
  refine ((Filter.eventually_cofinite.mp x.2).union χ.finite_setOf_dvd_conductor).subset
    fun v hv ↦ ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  exact hv (χ.finiteTest_eq_one h.2 ((mem_adicCompletionIntegers _ _ _).1 h.1))

theorem finiteTestFun_eq_zero {x : FiniteAdeleRing (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hx : 1 < Valued.v (x v)) : χ.finiteTestFun x = 0 :=
  finprod_eq_zero _ v (χ.finiteTest_eq_zero hx) (χ.hasFiniteMulSupport_finiteTest x)

theorem finiteTestFun_mem : χ.finiteTestFun ∈ finiteSchwartzBruhat K := by
  set I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := idealUnit χ.conductor χ.conductor_ne_bot
  have hadd : ∀ x, ∀ h ∈ idealFiniteAdeles I, χ.finiteTestFun (x + h) = χ.finiteTestFun x := by
    intro x h hh
    refine finprod_congr fun v ↦ ?_
    have hv := ((mem_idealFiniteAdeles I).1 hh) v
    rw [show ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (χ.conductor : FractionalIdeal (𝓞 K)⁰ K) from rfl,
      count_coeIdeal_eq_multiplicity v χ.conductor_ne_bot] at hv
    exact χ.finiteTest_add (x v) hv
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ ?_, ?_⟩
  · have hopen : ∀ᶠ y in 𝓝 x, y - x ∈ idealFiniteAdeles I :=
      ((continuous_id.sub continuous_const).tendsto' x 0 (sub_self x)).eventually
        ((isOpen_idealFiniteAdeles I).mem_nhds (zero_mem _))
    filter_upwards [hopen] with y hy
    have := hadd x (y - x) hy
    rwa [add_sub_cancel] at this
  · refine HasCompactSupport.intro (isCompact_idealFiniteAdeles 1) fun x hx ↦ ?_
    rw [SetLike.mem_coe, mem_idealFiniteAdeles] at hx
    push Not at hx
    obtain ⟨v, hv⟩ := hx
    simp only [Units.val_one, FractionalIdeal.count_one, neg_zero, exp_zero] at hv
    exact χ.finiteTestFun_eq_zero hv

def conductorPrimes : Finset (HeightOneSpectrum (𝓞 K)) := χ.finite_setOf_dvd_conductor.toFinset

theorem mem_conductorPrimes {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ χ.conductorPrimes ↔ v.asIdeal ∣ χ.conductor :=
  Set.Finite.mem_toFinset _

def conductorPart (b : (FiniteAdeleRing (𝓞 K) K)ˣ) : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ χ.conductorPrimes, finiteUnitsSingle v (finiteComponent v b)

open Classical in
theorem finiteComponent_conductorPart (b : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent v (χ.conductorPart b) =
      if v.asIdeal ∣ χ.conductor then finiteComponent v b else 1 := by
  rw [conductorPart, map_prod]
  split_ifs with hv
  · rw [Finset.prod_eq_single v (fun w _ hwv ↦ finiteComponent_finiteUnitsSingle_of_ne
      (Ne.symm hwv) _) (fun h ↦ absurd (χ.mem_conductorPrimes.2 hv) h),
      finiteComponent_finiteUnitsSingle]
  · refine Finset.prod_eq_one fun w hw ↦ finiteComponent_finiteUnitsSingle_of_ne ?_ _
    rintro rfl
    exact hv (χ.mem_conductorPrimes.1 hw)

theorem toIdele_ofFinite_conductorPart (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (χ.toIdele (ofFinite (χ.conductorPart b)) : ℂ) =
      ∏ v ∈ χ.conductorPrimes, (χ.localComponent v (finiteComponent v b) : ℂ) := by
  rw [conductorPart, map_prod, map_prod]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun v _ ↦ by rw [ofFinite_finiteUnitsSingle]; rfl)

theorem ord_ofFinite (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ord v (ofFinite b) =
      -log (Valued.v ((finiteComponent v b : (v.adicCompletion K)ˣ) : v.adicCompletion K)) :=
  rfl

theorem valued_eq_exp_ord (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((b : FiniteAdeleRing (𝓞 K) K) v) = exp (-ord v (ofFinite b)) := by
  rw [ord, neg_neg, exp_log (valued_ne_zero v (ofFinite b))]
  rfl

theorem isCoprime_of_count_eq_zero {I 𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) (hI : I ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0) : IsCoprime I 𝔪 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hM0 : M ≠ ⊥ := fun h0 ↦ h𝔪 (le_bot_iff.1 (h0 ▸ le_sup_right.trans hle))
  set v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hM0⟩
  have hv𝔪 : v.asIdeal ∣ 𝔪 := Ideal.dvd_iff_le.2 (le_sup_right.trans hle)
  have hvI : v.asIdeal ∣ I := Ideal.dvd_iff_le.2 (le_sup_left.trans hle)
  have := h v hv𝔪
  rw [count_coeIdeal_eq_multiplicity v hI] at this
  exact (multiplicity_pos_of_dvd hvI).ne' (by exact_mod_cast this)

theorem idealOfExponents_ne_bot {n : HeightOneSpectrum (𝓞 K) →₀ ℤ} (hn : ∀ v, 0 ≤ n v) :
    idealOfExponents n ≠ ⊥ := by
  intro h
  have h1 := coeIdeal_idealOfExponents (K := K) hn
  rw [h, FractionalIdeal.coeIdeal_bot, Finsupp.prod] at h1
  exact (Finset.prod_ne_zero_iff.2 fun v _ ↦ zpow_ne_zero _
    (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)) h1.symm

theorem count_idealOfExponents {n : HeightOneSpectrum (𝓞 K) →₀ ℤ} (hn : ∀ v, 0 ≤ n v)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v ((idealOfExponents n : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      n v := by
  rw [coeIdeal_idealOfExponents hn, FractionalIdeal.count_finsuppProd]

open Classical in

theorem finiteTestFun_mul_toIdele (b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    χ.finiteTestFun b * (χ.toIdele (ofFinite b) : ℂ) =
      if ∀ v, 0 ≤ ord v (ofFinite b) then χ.coeff (idealOfExponents (ordFinsupp K (ofFinite b)))
      else 0 := by
  have hval := valued_eq_exp_ord b
  by_cases hpos : ∀ v, 0 ≤ ord v (ofFinite b)
  · rw [if_pos hpos]
    set n := ordFinsupp K (ofFinite b) with hn_def
    have hn : ∀ v, n v = ord v (ofFinite b) := fun v ↦ rfl
    have hn0 : ∀ v, 0 ≤ n v := fun v ↦ (hn v).symm ▸ hpos v
    by_cases hcop : ∀ v, v.asIdeal ∣ χ.conductor → ord v (ofFinite b) = 0
    ·
      have hI0 := idealOfExponents_ne_bot hn0
      have hIc : IsCoprime (idealOfExponents n) χ.conductor :=
        isCoprime_of_count_eq_zero χ.conductor_ne_bot hI0 fun v hv ↦ by
          rw [count_idealOfExponents hn0, hn, hcop v hv]
      set u := χ.conductorPart b
      set b' := b * u⁻¹
      have hcomp : ∀ v, finiteComponent v b' =
          if v.asIdeal ∣ χ.conductor then 1 else finiteComponent v b := by
        intro v
        rw [map_mul, map_inv, χ.finiteComponent_conductorPart]
        split_ifs
        · exact mul_inv_cancel _
        · rw [inv_one, mul_one]
      have hord : ∀ v, ord v (ofFinite b') = ord v (ofFinite b) := by
        intro v
        rw [ord_ofFinite, hcomp]
        split_ifs with hv
        · rw [Units.val_one, map_one, log_one, neg_zero, hcop v hv]
        · rfl
      have hfrac : toFractionalIdeal (ofFinite b') =
          idealUnit (idealOfExponents n) hI0 := by
        rw [toFractionalIdeal_eq_iff]
        intro v
        rw [hord, ← hn]
        exact (count_idealOfExponents hn0 v).symm
      have hmem : ofFinite b' ∈ primeToLevel χ.conductor := by
        refine mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩
        rw [← finiteComponent_toFinite, toFinite_ofFinite, hcomp, if_pos hv]
        exact one_mem _
      have hchar : χ.coeff (idealOfExponents n) = χ.toIdele (ofFinite b') := by
        rw [χ.coeff_of_mem ⟨hI0, hIc⟩]
        exact congrArg (fun z : Circle ↦ (z : ℂ)) (χ.idealCharacter_apply hmem _ hfrac)
      have htest : χ.finiteTestFun b =
          ∏ v ∈ χ.conductorPrimes, ((χ.localComponent v (finiteComponent v b) : ℂ))⁻¹ := by
        rw [finiteTestFun, finprod_eq_prod_of_mulSupport_subset _ (s := χ.conductorPrimes)]
        · refine Finset.prod_congr rfl fun v hv ↦ ?_
          have hv' := χ.mem_conductorPrimes.1 hv
          have h1 : Valued.v (((finiteComponent v b : (v.adicCompletion K)ˣ)) :
              v.adicCompletion K) = 1 := by
            rw [coe_finiteComponent, hval, hcop v hv', neg_zero, exp_zero]
          rw [← χ.finiteTest_of_dvd hv' _ h1, coe_finiteComponent]
        · intro v hv
          by_contra hvD
          have hv' : ¬ v.asIdeal ∣ χ.conductor := fun h ↦ hvD (χ.mem_conductorPrimes.2 h)
          refine hv (χ.finiteTest_eq_one hv' ?_)
          rw [hval, ← exp_zero, exp_le_exp]
          linarith [hpos v]
      have hne : ∏ v ∈ χ.conductorPrimes, (χ.localComponent v (finiteComponent v b) : ℂ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun v _ ↦ Circle.coe_ne_zero _
      have hsplit : (χ.toIdele (ofFinite b) : ℂ) = (χ.toIdele (ofFinite b') : ℂ) *
          ∏ v ∈ χ.conductorPrimes, (χ.localComponent v (finiteComponent v b) : ℂ) := by
        rw [← toIdele_ofFinite_conductorPart, ← Circle.coe_mul, ← map_mul, ← map_mul,
          inv_mul_cancel_right]
      rw [hsplit, htest, hchar, Finset.prod_inv_distrib]
      field_simp
    ·
      push Not at hcop
      obtain ⟨v, hv, hv0⟩ := hcop
      have hvpos : 0 < ord v (ofFinite b) := lt_of_le_of_ne (hpos v) (Ne.symm hv0)
      have h1 : χ.finiteTestFun b = 0 := by
        refine finprod_eq_zero _ v (χ.finiteTest_eq_zero_of_dvd hv ?_)
          (χ.hasFiniteMulSupport_finiteTest b)
        rw [hval, ← exp_zero]
        intro h
        exact hv0 (by have := exp_injective h; omega)
      have hdvd : v.asIdeal ∣ idealOfExponents n := by
        have hsupp : v ∈ n.support := Finsupp.mem_support_iff.2 (by rw [hn]; omega)
        refine (dvd_pow_self v.asIdeal ?_).trans
          (Finset.dvd_prod_of_mem (fun w ↦ w.asIdeal ^ (n w).toNat) hsupp)
        rw [hn]
        omega
      have h2 : χ.coeff (idealOfExponents n) = 0 :=
        χ.coeff_of_not fun h ↦ not_dvd_of_isCoprime h.2 hv hdvd
      rw [h1, zero_mul, h2]
  · rw [if_neg hpos]
    push Not at hpos
    obtain ⟨v, hv⟩ := hpos
    rw [χ.finiteTestFun_eq_zero (v := v) (by rw [hval, ← exp_zero, exp_lt_exp]; omega), zero_mul]

theorem finiteModule_ofFinite_eq {b : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hpos : ∀ v, 0 ≤ ord v (ofFinite b)) :
    finiteModule (ofFinite b) =
      ((Ideal.absNorm (idealOfExponents (ordFinsupp K (ofFinite b))) : ℝ))⁻¹ := by
  have h := finiteModule_rpow_eq (ofFinite b) 1
  rw [Real.rpow_one, zetaWeight_eq_absNorm (k := ordFinsupp K (ofFinite b)) hpos,
    Real.rpow_one] at h
  exact h

open Classical in

def orderTerm (s : ℂ) (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) : ℂ :=
  if ∀ v, 0 ≤ n v then χ.coeff (idealOfExponents n) *
    (Ideal.absNorm (idealOfExponents n) : ℂ) ^ (-s) else 0

theorem finiteTestFun_mul_toIdele_mul_cpow (b : (FiniteAdeleRing (𝓞 K) K)ˣ) (s : ℂ) :
    χ.finiteTestFun b * (χ.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) : ℝ) : ℂ) ^ s =
      χ.orderTerm s (ordFinsupp K (ofFinite b)) := by
  rw [χ.finiteTestFun_mul_toIdele, orderTerm]
  by_cases hpos : ∀ v, 0 ≤ ord v (ofFinite b)
  · rw [if_pos hpos, if_pos (show ∀ v, 0 ≤ (ordFinsupp K (ofFinite b)) v from hpos),
      finiteModule_ofFinite_eq hpos]
    have hN : (0 : ℝ) < Ideal.absNorm (idealOfExponents (ordFinsupp K (ofFinite b))) := by
      have := idealOfExponents_ne_bot (K := K) (n := ordFinsupp K (ofFinite b)) hpos
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h ↦ this (Ideal.absNorm_eq_zero_iff.1 h))
    have harg : ((Ideal.absNorm (idealOfExponents (ordFinsupp K (ofFinite b))) : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.ofReal_natCast, Complex.natCast_arg]
      exact Real.pi_pos.ne
    congr 1
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]
  · rw [if_neg hpos, if_neg (show ¬ ∀ v, 0 ≤ (ordFinsupp K (ofFinite b)) v from hpos), zero_mul]

theorem exists_idealOfExponents_eq {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ n : HeightOneSpectrum (𝓞 K) →₀ ℤ, (∀ v, 0 ≤ n v) ∧ idealOfExponents n = I := by
  set n := countFinsupp (idealUnit I hI)
  have hn : ∀ v, n v = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := fun v ↦ rfl
  have hn0 : ∀ v, 0 ≤ n v := fun v ↦ by
    rw [hn]; exact FractionalIdeal.count_coe_nonneg K v I
  refine ⟨n, hn0, ?_⟩
  have h : idealUnit (idealOfExponents n) (idealOfExponents_ne_bot hn0) = idealUnit I hI := by
    rw [fractionalIdealUnits_eq_iff]
    intro v
    change FractionalIdeal.count K v ((idealOfExponents n : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
    rw [count_idealOfExponents hn0, hn]
  exact FractionalIdeal.coeIdeal_injective (congrArg Units.val h)

theorem hasSum_orderTerm {s : ℂ} (hs : 1 < s.re) : HasSum (χ.orderTerm s) (χ.LFunction s) := by
  set T := {n : HeightOneSpectrum (𝓞 K) →₀ ℤ | ∀ v, 0 ≤ n v}
  have hinj : Function.Injective fun n : T ↦ idealOfExponents (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
    fun n m h ↦ Subtype.ext (idealOfExponents_injOn n.2 m.2 h)
  have h1 := χ.hasSum_LFunction hs
  rw [← hinj.hasSum_iff] at h1
  · rw [← hasSum_subtype_iff_of_support_subset (s := T)]
    · convert h1 using 1
      funext n
      simp only [Function.comp_apply, orderTerm]
      rw [if_pos (show ∀ v, 0 ≤ (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) v from n.2)]
    · intro n hn
      by_contra h
      exact hn (by simp only [orderTerm]; rw [if_neg (show ¬ ∀ v, 0 ≤ n v from h)])
  · intro I hI
    by_cases h0 : I = ⊥
    · rw [h0, coeff_bot, zero_mul]
    · obtain ⟨n, hn0, hn⟩ := exists_idealOfExponents_eq h0
      exact absurd ⟨⟨n, hn0⟩, hn⟩ hI

theorem exists_ordFinsupp_eq (n : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    ∃ b : (FiniteAdeleRing (𝓞 K) K)ˣ, ordFinsupp K (ofFinite b) = n := by
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    rw [Filter.eventually_cofinite]
    exact n.support.finite_toSet.subset fun v hv ↦ Finsupp.mem_support_iff.2 hv
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K)
    (∏ᶠ v, primeIdealUnit v ^ n v)
  refine ⟨toFinite K x, Finsupp.ext fun v ↦ ?_⟩
  change ord v x = n v
  rw [← count_toFractionalIdeal, hx]
  exact count_finprod_primeIdealUnit_zpow _ hfin v

theorem hasSum_finiteTestFun {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦
      χ.finiteTestFun c.out * (χ.toIdele (ofFinite c.out) : ℂ) *
        ((finiteModule (ofFinite c.out) : ℝ) : ℂ) ^ s) (χ.LFunction s) := by
  simp_rw [χ.finiteTestFun_mul_toIdele_mul_cpow]
  have h := χ.hasSum_orderTerm hs
  rw [← ordFinsupp_ofFinite_out_injective.hasSum_iff] at h
  · exact h
  · intro n hn
    obtain ⟨b, hb⟩ := exists_ordFinsupp_eq n
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (finiteIntegralUnits K) b
    refine absurd ⟨(b : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K), ?_⟩ hn
    change ordFinsupp K (ofFinite (QuotientGroup.mk (s := finiteIntegralUnits K) b).out) = n
    rw [hw, ordFinsupp_ofFinite_mul b w.2, hb]

end HeckeCharacter

end

end GroundTheory.Global
