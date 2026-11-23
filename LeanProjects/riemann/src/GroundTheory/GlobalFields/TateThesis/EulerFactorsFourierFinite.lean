import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInverse
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
  MeasureTheory WithZero
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def differentExp (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← exp_log hx, exp_le_exp]
    rw [← exp_log hx, ← exp_zero, exp_lt_exp] at h
    omega

theorem multiplicity_finprod_asIdeal_pow {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a : HeightOneSpectrum R → ℕ} (ha : (Function.support a).Finite) (v : HeightOneSpectrum R) :
    multiplicity v.asIdeal (∏ᶠ w, w.asIdeal ^ a w) = a v := by
  classical
  set I := ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w
  have hI : I ≠ ⊥ := finprod_asIdeal_pow_ne_bot a
  have h1 : a v ≤ multiplicity v.asIdeal I := (finprod_asIdeal_pow_dvd_iff ha hI).1 dvd_rfl v
  refine le_antisymm ?_ h1
  by_contra h2
  push Not at h2
  set b : HeightOneSpectrum R → ℕ := fun w ↦ a w + if w = v then 1 else 0
  have hb : (Function.support b).Finite := (ha.union (Set.finite_singleton v)).subset fun w hw ↦ by
    by_contra hw'
    simp only [Set.mem_union, Function.mem_support, Set.mem_singleton_iff, not_or, not_not] at hw'
    exact hw (by simp [b, hw'.1, hw'.2])
  have hdvd : (∏ᶠ w, w.asIdeal ^ b w) ∣ I := by
    refine (finprod_asIdeal_pow_dvd_iff hb hI).2 fun w ↦ ?_
    by_cases hw : w = v
    · rw [hw]
      show a v + (if v = v then 1 else 0) ≤ _
      rw [if_pos rfl]
      omega
    · simp only [b, if_neg hw, add_zero]
      exact (finprod_asIdeal_pow_dvd_iff ha hI).1 dvd_rfl w
  have hfa : Function.HasFiniteMulSupport fun w : HeightOneSpectrum R ↦ w.asIdeal ^ a w := by
    rw [Function.HasFiniteMulSupport, mulSupport_asIdeal_pow]; exact ha
  have hfv : Function.HasFiniteMulSupport fun w : HeightOneSpectrum R ↦
      w.asIdeal ^ (if w = v then 1 else 0) := by
    refine (Set.finite_singleton v).subset fun w hw ↦ ?_
    by_contra hw'
    exact hw (by simp [Set.mem_singleton_iff.not.1 hw'])
  have hsplit : (∏ᶠ w, w.asIdeal ^ b w) = I * v.asIdeal := by
    simp only [b, pow_add]
    rw [finprod_mul_distrib hfa hfv]
    congr 1
    rw [finprod_eq_single _ v fun w hw ↦ by simp [hw], if_pos rfl, pow_one]
  rw [hsplit] at hdvd
  have h1' : I * v.asIdeal ∣ I * 1 := by rwa [mul_one]
  have hv1 := (mul_dvd_mul_iff_left (show I ≠ 0 from hI)).1 h1'
  rw [Ideal.dvd_iff_le, Ideal.one_eq_top, top_le_iff] at hv1
  exact v.isPrime.ne_top hv1

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def condExp (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v (χ.conductor : FractionalIdeal (𝓞 K)⁰ K)

theorem condExp_eq (v : HeightOneSpectrum (𝓞 K)) :
    χ.condExp v = multiplicity v.asIdeal χ.conductor :=
  count_coeIdeal_eq_multiplicity v χ.conductor_ne_bot

theorem condExp_eq_zero {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor) :
    χ.condExp v = 0 := by
  rw [condExp_eq, multiplicity_eq_zero.2 hv, Nat.cast_zero]

theorem one_le_condExp {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor) :
    1 ≤ χ.condExp v := by
  rw [condExp_eq]
  exact_mod_cast multiplicity_pos_of_dvd hv

theorem finiteTestFun_add (x : FiniteAdeleRing (𝓞 K) K) {h : FiniteAdeleRing (𝓞 K) K}
    (hh : ∀ v, Valued.v (h v) ≤ exp (-χ.condExp v)) :
    χ.finiteTestFun (x + h) = χ.finiteTestFun x :=
  finprod_congr fun v ↦ χ.finiteTest_add (x v) (by rw [← χ.condExp_eq]; exact hh v)

theorem valued_le_one_of_finiteTestFun_ne_zero {x : FiniteAdeleRing (𝓞 K) K}
    (hx : χ.finiteTestFun x ≠ 0) (v : HeightOneSpectrum (𝓞 K)) : Valued.v (x v) ≤ 1 := by
  by_contra h
  exact hx (χ.finiteTestFun_eq_zero (not_le.1 h))

theorem finiteTestFun_one : χ.finiteTestFun 1 = 1 := by
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  change χ.finiteTest v 1 = 1
  by_cases hv : v.asIdeal ∣ χ.conductor
  · have h := χ.finiteTest_of_dvd hv 1 (by simp)
    rw [Units.val_one] at h
    rw [h, map_one, Circle.coe_one, inv_one]
  · exact χ.finiteTest_eq_one hv (by simp)

theorem finiteFourier_add {y h : FiniteAdeleRing (𝓞 K) K}
    (hh : ∀ v, Valued.v (h v) ≤ exp (differentExp v)) :
    finiteFourier K χ.finiteTestFun (y + h) = finiteFourier K χ.finiteTestFun y := by
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : χ.finiteTestFun x = 0
  · simp [hx]
  have hψ : finiteAdelicChar K (x * h) = 1 := by
    refine finiteAdelicChar_eq_one_of_mem fun v ↦ ?_
    change x v * h v ∈ localInvDifferent v
    rw [mem_localInvDifferent_iff_valued, Valuation.map_mul]
    calc Valued.v (x v) * Valued.v (h v) ≤ 1 * exp (differentExp v) :=
          mul_le_mul' (χ.valued_le_one_of_finiteTestFun_ne_zero hx v) (hh v)
      _ = _ := one_mul _
  simp only
  rw [mul_add, AddChar.map_add_eq_mul, hψ, mul_one]

theorem finiteFourier_eq_zero_of_not_le {y : FiniteAdeleRing (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hy : ¬ Valued.v (y v) ≤ exp (χ.condExp v + differentExp v)) :
    finiteFourier K χ.finiteTestFun y = 0 := by
  by_contra hF
  set I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := idealUnit χ.conductor χ.conductor_ne_bot
  have hψ : ∀ h ∈ idealFiniteAdeles I, finiteAdelicChar K (h * y) = 1 := by
    intro h hh
    have hh' : ∀ w, Valued.v (h w) ≤ exp (-χ.condExp w) := (mem_idealFiniteAdeles I).1 hh
    have hshift : finiteFourier K χ.finiteTestFun y =
        (finiteAdelicChar K (h * y) : ℂ) * finiteFourier K χ.finiteTestFun y := by
      conv_lhs => rw [finiteFourier, ← integral_add_right_eq_self _ h]
      rw [finiteFourier, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      rw [χ.finiteTestFun_add x hh', add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have h1 : ((finiteAdelicChar K (h * y) : ℂ) - 1) * finiteFourier K χ.finiteTestFun y = 0 := by
      rw [sub_mul, ← hshift, one_mul, sub_self]
    have h2 := (mul_eq_zero.1 h1).resolve_right hF
    exact Circle.coe_eq_one.1 (sub_eq_zero.1 h2)
  have hmem := (forall_finiteAdelicChar_mul_eq_one_iff I y).1 hψ v
  rw [count_traceDualIdeal, neg_neg] at hmem
  exact hy hmem

def conductorChar (u : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  ∏ v ∈ χ.conductorPrimes, (χ.localComponent v (finiteComponent v u) : ℂ)

theorem conductorChar_ne_zero (u : (FiniteAdeleRing (𝓞 K) K)ˣ) : χ.conductorChar u ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ ↦ Circle.coe_ne_zero _

open Classical in

theorem finiteTest_mul {v : HeightOneSpectrum (𝓞 K)} (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) (x : v.adicCompletion K) :
    χ.finiteTest v (u * x) =
      (if v.asIdeal ∣ χ.conductor then ((χ.localComponent v u : ℂ))⁻¹ else 1) *
        χ.finiteTest v x := by
  have hv' : Valued.v ((u : v.adicCompletion K) * x) = Valued.v x := by rw [map_mul, hu, one_mul]
  by_cases hv : v.asIdeal ∣ χ.conductor
  · rw [if_pos hv]
    by_cases hx : Valued.v x = 1
    · have hx0 : x ≠ 0 := fun h0 ↦ by simp [h0] at hx
      have e1 := χ.finiteTest_of_dvd hv (u * Units.mk0 x hx0) (by
        rw [Units.val_mul, Units.val_mk0, hv', hx])
      have e2 := χ.finiteTest_of_dvd hv (Units.mk0 x hx0) (by rw [Units.val_mk0, hx])
      simp only [Units.val_mul, Units.val_mk0] at e1 e2
      rw [e1, e2, map_mul, Circle.coe_mul, mul_inv]
    · rw [χ.finiteTest_eq_zero_of_dvd hv hx, χ.finiteTest_eq_zero_of_dvd hv (by rwa [hv']),
        mul_zero]
  · rw [if_neg hv, one_mul]
    unfold finiteTest
    simp only [if_neg hv, hv']

theorem finiteTestFun_units_mul (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hu : ∀ v, Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1) (x : FiniteAdeleRing (𝓞 K) K) :
    χ.finiteTestFun ((u : FiniteAdeleRing (𝓞 K) K) * x) = (χ.conductorChar u)⁻¹ * χ.finiteTestFun x := by
  classical
  set c : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ if v.asIdeal ∣ χ.conductor then
    ((χ.localComponent v (finiteComponent v u) : ℂ))⁻¹ else 1
  have hc : ∀ v, χ.finiteTest v (((u : FiniteAdeleRing (𝓞 K) K) * x) v) =
      c v * χ.finiteTest v (x v) := fun v ↦ by
    have := χ.finiteTest_mul (finiteComponent v u) (by rw [coe_finiteComponent]; exact hu v) (x v)
    rw [coe_finiteComponent] at this
    exact this
  have hfc : Function.HasFiniteMulSupport c :=
    χ.finite_setOf_dvd_conductor.subset fun v hv ↦ by
      by_contra h
      exact hv (if_neg h)
  rw [finiteTestFun, finprod_congr hc, finprod_mul_distrib hfc (χ.hasFiniteMulSupport_finiteTest x),
    conductorChar, ← Finset.prod_inv_distrib]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := χ.conductorPrimes)]
  · exact Finset.prod_congr rfl fun v hv ↦ if_pos (χ.mem_conductorPrimes.1 hv)
  · intro v hv
    by_contra h
    exact hv (if_neg fun h' ↦ h (χ.mem_conductorPrimes.2 h'))

theorem map_units_mul_finiteAdeleMeasure (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hu : ∀ v, Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1) :
    (finiteAdeleMeasure K).map (fun x ↦ (u : FiniteAdeleRing (𝓞 K) K) * x) = finiteAdeleMeasure K := by
  rw [map_mul_left_finiteAdeleMeasure]
  have h1 : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      ‖((u⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v‖₊) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by
      have hmul := units_mul_inv_apply u v
      have hinv : Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
        have := congrArg Valued.v hmul
        rwa [map_mul, hu v, one_mul, map_one] at this
      have hi : IsIntegralUnitAt u⁻¹ v :=
        ⟨(mem_adicCompletionIntegers _ _ _).2 hinv.le,
          (mem_adicCompletionIntegers _ _ _).2 (by rw [inv_inv, hu v])⟩
      rw [← NNReal.coe_eq_one, coe_nnnorm]
      exact norm_eq_one_of_isIntegralUnitAt hi
  rw [h1, ENNReal.coe_one, one_smul]

theorem finiteFourier_units_mul (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hu : ∀ v, Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1) (y : FiniteAdeleRing (𝓞 K) K) :
    finiteFourier K χ.finiteTestFun ((u : FiniteAdeleRing (𝓞 K) K) * y) =
      χ.conductorChar u * finiteFourier K χ.finiteTestFun y := by
  have hemb : MeasurableEmbedding fun x : FiniteAdeleRing (𝓞 K) K ↦
      (u : FiniteAdeleRing (𝓞 K) K) * x := by
    have h : MeasurableEmbedding fun x : FiniteAdeleRing (𝓞 K) K ↦ u • x :=
      (Homeomorph.smul u).toMeasurableEquiv.measurableEmbedding
    simpa only [Units.smul_def, smul_eq_mul] using h
  set g : FiniteAdeleRing (𝓞 K) K → ℂ := fun x ↦
    χ.finiteTestFun x * (finiteAdelicChar K (x * y) : ℂ)
  have h := hemb.integral_map (μ := finiteAdeleMeasure K) g
  rw [map_units_mul_finiteAdeleMeasure u hu] at h
  rw [finiteFourier, finiteFourier, ← integral_const_mul]
  change _ = ∫ x, χ.conductorChar u * g x ∂finiteAdeleMeasure K
  rw [integral_const_mul, h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [g, χ.finiteTestFun_units_mul u hu]
  rw [show (u : FiniteAdeleRing (𝓞 K) K) * x * y = x * ((u : FiniteAdeleRing (𝓞 K) K) * y) by ring]
  field_simp [χ.conductorChar_ne_zero u]

theorem multiplicity_conductor (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal χ.conductor = conductorExponentAt (χ.toIdele.comp ofFinite) v :=
  multiplicity_finprod_asIdeal_pow (finite_support_conductorExponentAt Circle.noSmallSubgroups _
    (χ.continuous_toIdele.comp continuous_ofFinite)) v

theorem exists_mem_unitsLevel_ne_one {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor) :
    ∃ u ∈ unitsLevel v (multiplicity v.asIdeal χ.conductor - 1), χ.localComponent v u ≠ 1 := by
  have hloc : ((χ.toIdele.comp ofFinite).comp (finiteUnitsSingle v)) =
      (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle) := by
    ext a
    simp only [MonoidHom.comp_apply, ofFinite_finiteUnitsSingle]
    rfl
  have hcont : Continuous ((χ.toIdele.comp ofFinite).comp (finiteUnitsSingle v)) :=
    (χ.continuous_toIdele.comp continuous_ofFinite).comp (continuous_finiteUnitsSingle v)
  have hn := multiplicity_pos_of_dvd hv
  have hnot : ¬ unitsLevel v (multiplicity v.asIdeal χ.conductor - 1) ≤
      ((χ.toIdele.comp ofFinite).comp (finiteUnitsSingle v)).ker := by
    rw [unitsLevel_le_ker_iff v Circle.noSmallSubgroups _ hcont]
    change ¬ conductorExponentAt (χ.toIdele.comp ofFinite) v ≤ _
    rw [← χ.multiplicity_conductor]
    omega
  rw [hloc] at hnot
  obtain ⟨u, hu, hu1⟩ := Set.not_subset.1 hnot
  exact ⟨u, hu, hu1⟩

theorem finiteFourier_eq_zero_of_le {y : FiniteAdeleRing (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ χ.conductor)
    (hy : Valued.v (y v) ≤ exp (χ.condExp v + differentExp v - 1)) :
    finiteFourier K χ.finiteTestFun y = 0 := by
  obtain ⟨a, ha, ha1⟩ := χ.exists_mem_unitsLevel_ne_one hv
  set u := finiteUnitsSingle v a
  have hn := multiplicity_pos_of_dvd hv
  have hu : ∀ w, Valued.v ((u : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
    intro w
    rw [← coe_finiteComponent]
    by_cases hw : w = v
    · subst hw
      rw [finiteComponent_finiteUnitsSingle]
      exact ha.1
    · rw [finiteComponent_finiteUnitsSingle_of_ne hw]
      simp
  have hchar : χ.conductorChar u = χ.localComponent v a := by
    rw [conductorChar, Finset.prod_eq_single v (fun w _ hw ↦ by
        rw [finiteComponent_finiteUnitsSingle_of_ne hw, map_one, Circle.coe_one])
      (fun h ↦ absurd (χ.mem_conductorPrimes.2 hv) h), finiteComponent_finiteUnitsSingle]
  have hh : ∀ w, Valued.v ((((u : FiniteAdeleRing (𝓞 K) K) * y - y)) w) ≤ exp (differentExp w) := by
    intro w
    change Valued.v ((u : FiniteAdeleRing (𝓞 K) K) w * y w - y w) ≤ _
    rw [← coe_finiteComponent]
    by_cases hw : w = v
    · subst hw
      rw [finiteComponent_finiteUnitsSingle, ← sub_one_mul, map_mul]
      calc Valued.v ((a : w.adicCompletion K) - 1) * Valued.v (y w)
          ≤ exp (-((multiplicity w.asIdeal χ.conductor - 1 : ℕ) : ℤ)) *
              exp (χ.condExp w + differentExp w - 1) := mul_le_mul' ha.2 hy
        _ = exp (differentExp w) := by
          rw [← exp_add, χ.condExp_eq]
          congr 1
          omega
    · rw [finiteComponent_finiteUnitsSingle_of_ne hw, Units.val_one, one_mul, sub_self, map_zero]
      exact zero_le
  have h1 := χ.finiteFourier_units_mul u hu y
  rw [show (u : FiniteAdeleRing (𝓞 K) K) * y = y + ((u : FiniteAdeleRing (𝓞 K) K) * y - y) by ring,
    χ.finiteFourier_add hh, hchar] at h1
  have h2 : ((χ.localComponent v a : ℂ) - 1) * finiteFourier K χ.finiteTestFun y = 0 := by
    rw [sub_mul, ← h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 fun h ↦ ha1 (Circle.coe_eq_one.1 h))

open Classical in

def unitOrOne {F : Type*} [GroupWithZero F] (x : F) : Fˣ :=
  if h : x = 0 then 1 else Units.mk0 x h

theorem coe_unitOrOne {F : Type*} [GroupWithZero F] {x : F} (hx : x ≠ 0) :
    ((unitOrOne x : Fˣ) : F) = x := by
  rw [unitOrOne, dif_neg hx, Units.val_mk0]

theorem finiteTestFun_eq_zero_of_dvd {x : FiniteAdeleRing (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ χ.conductor) (hx : Valued.v (x v) ≠ 1) : χ.finiteTestFun x = 0 :=
  finprod_eq_zero _ v (χ.finiteTest_eq_zero_of_dvd hv hx) (χ.hasFiniteMulSupport_finiteTest x)

theorem finiteFourier_finiteTestFun (δ : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hδ : ∀ v, Valued.v ((δ : FiniteAdeleRing (𝓞 K) K) v) = exp (-(χ.condExp v + differentExp v)))
    (y : FiniteAdeleRing (𝓞 K) K) :
    finiteFourier K χ.finiteTestFun y =
      finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) *
        (χ⁻¹).finiteTestFun ((δ : FiniteAdeleRing (𝓞 K) K) * y) := by
  classical
  set z := (δ : FiniteAdeleRing (𝓞 K) K) * y with hz_def
  have hz : ∀ v, Valued.v (z v) = exp (-(χ.condExp v + differentExp v)) * Valued.v (y v) :=
    fun v ↦ by
      change Valued.v ((δ : FiniteAdeleRing (𝓞 K) K) v * y v) = _
      rw [map_mul, hδ]
  have hyz : ∀ v, Valued.v (y v) = exp (χ.condExp v + differentExp v) * Valued.v (z v) := fun v ↦ by
    rw [hz, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  have hcond : (χ⁻¹).conductor = χ.conductor := χ.conductor_inv
  by_cases ha : ∃ v, 1 < Valued.v (z v)
  ·
    obtain ⟨v, hv⟩ := ha
    rw [(χ⁻¹).finiteTestFun_eq_zero hv, mul_zero]
    refine χ.finiteFourier_eq_zero_of_not_le (v := v) fun hle ↦ ?_
    have h1 : Valued.v (z v) ≤ 1 := by
      rw [hz]
      calc exp (-(χ.condExp v + differentExp v)) * Valued.v (y v)
          ≤ exp (-(χ.condExp v + differentExp v)) * exp (χ.condExp v + differentExp v) :=
            mul_le_mul' le_rfl hle
        _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    exact absurd h1 (not_le.2 hv)
  push Not at ha
  by_cases hb : ∃ v, v.asIdeal ∣ χ.conductor ∧ Valued.v (z v) ≠ 1
  ·
    obtain ⟨v, hv, hzv⟩ := hb
    rw [(χ⁻¹).finiteTestFun_eq_zero_of_dvd (by rw [hcond]; exact hv) hzv, mul_zero]
    refine χ.finiteFourier_eq_zero_of_le hv ?_
    rw [hyz]
    calc exp (χ.condExp v + differentExp v) * Valued.v (z v)
        ≤ exp (χ.condExp v + differentExp v) * exp (-1) :=
          mul_le_mul' le_rfl (le_exp_neg_one_of_lt_one (lt_of_le_of_ne (ha v) hzv))
      _ = exp (χ.condExp v + differentExp v - 1) := by rw [← exp_add]; rfl
  push Not at hb

  set D := χ.conductorPrimes
  set u : (FiniteAdeleRing (𝓞 K) K)ˣ := ∏ v ∈ D, finiteUnitsSingle v (unitOrOne (z v)) with hu_def
  have hz0 : ∀ v ∈ D, z v ≠ 0 := fun v hv h0 ↦ by
    have := hb v (χ.mem_conductorPrimes.1 hv)
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hcomp : ∀ w, finiteComponent w u = if w ∈ D then unitOrOne (z w) else 1 := by
    intro w
    rw [hu_def, map_prod]
    split_ifs with hw
    · rw [Finset.prod_eq_single w (fun x _ hxw ↦ finiteComponent_finiteUnitsSingle_of_ne
        (Ne.symm hxw) _) (fun h ↦ absurd hw h), finiteComponent_finiteUnitsSingle]
    · refine Finset.prod_eq_one fun x hx ↦ finiteComponent_finiteUnitsSingle_of_ne ?_ _
      rintro rfl
      exact hw hx
  have hcoe : ∀ w, ((u : FiniteAdeleRing (𝓞 K) K) w) = if w ∈ D then z w else 1 := by
    intro w
    rw [← coe_finiteComponent, hcomp]
    split_ifs with hw
    · exact coe_unitOrOne (hz0 w hw)
    · rfl
  have hu : ∀ w, Valued.v ((u : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
    intro w
    rw [hcoe]
    split_ifs with hw
    · exact hb w (χ.mem_conductorPrimes.1 hw)
    · exact map_one _

  set h : FiniteAdeleRing (𝓞 K) K :=
    ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) *
      ((u : FiniteAdeleRing (𝓞 K) K) - z) with hh_def
  have hyh : y + h = ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) *
      (u : FiniteAdeleRing (𝓞 K) K) := by
    rw [hh_def, mul_sub, hz_def, Units.inv_mul_cancel_left]
    ring
  have hδinv : ∀ w, Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w) =
      exp (χ.condExp w + differentExp w) := fun w ↦ by
    have := congrArg Valued.v (units_mul_inv_apply δ w)
    rw [map_mul, hδ, map_one] at this
    calc _ = exp (χ.condExp w + differentExp w) *
          (exp (-(χ.condExp w + differentExp w)) *
            Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w)) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ = _ := by rw [this, mul_one]
  have hhle : ∀ w, Valued.v (h w) ≤ exp (differentExp w) := by
    intro w
    change Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w *
      ((u : FiniteAdeleRing (𝓞 K) K) w - z w)) ≤ _
    rw [map_mul, hδinv, hcoe]
    split_ifs with hw
    · rw [sub_self, map_zero, mul_zero]
      exact zero_le
    · have hw' : ¬ w.asIdeal ∣ χ.conductor := fun h ↦ hw (χ.mem_conductorPrimes.2 h)
      rw [χ.condExp_eq_zero hw', zero_add]
      calc exp (differentExp w) * Valued.v (1 - z w) ≤ exp (differentExp w) * 1 :=
            mul_le_mul' le_rfl ((Valuation.map_sub _ _ _).trans
              (max_le (by rw [map_one]) (ha w)))
        _ = _ := mul_one _
  have hF : finiteFourier K χ.finiteTestFun y =
      χ.conductorChar u * finiteFourier K χ.finiteTestFun
        ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) := by
    rw [← χ.finiteFourier_add hhle, hyh, mul_comm, χ.finiteFourier_units_mul u hu]

  have htest : (χ⁻¹).finiteTestFun z = χ.conductorChar u := by
    rw [finiteTestFun, finprod_eq_prod_of_mulSupport_subset _ (s := D), conductorChar]
    · refine Finset.prod_congr rfl fun v hv ↦ ?_
      have hv' := χ.mem_conductorPrimes.1 hv
      have h1 : Valued.v (((unitOrOne (z v) : (v.adicCompletion K)ˣ)) : v.adicCompletion K) = 1 := by
        rw [coe_unitOrOne (hz0 v hv)]
        exact hb v hv'
      have e := (χ⁻¹).finiteTest_of_dvd (by rw [hcond]; exact hv') _ h1
      rw [coe_unitOrOne (hz0 v hv)] at e
      rw [e, localComponent_inv, Circle.coe_inv, inv_inv, hcomp, if_pos hv]
    · intro v hv
      by_contra hvD
      have hv' : ¬ v.asIdeal ∣ (χ⁻¹).conductor := by
        rw [hcond]
        exact fun h ↦ hvD (χ.mem_conductorPrimes.2 h)
      exact hv ((χ⁻¹).finiteTest_eq_one hv' (ha v))
  rw [hF, htest, mul_comm]

theorem finiteFourier_finiteTestFun_ne_zero (δ : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hδ : ∀ v, Valued.v ((δ : FiniteAdeleRing (𝓞 K) K) v) = exp (-(χ.condExp v + differentExp v))) :
    finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ≠
      0 := by
  intro h0
  have hF : finiteFourier K χ.finiteTestFun = 0 := funext fun y ↦ by
    rw [χ.finiteFourier_finiteTestFun δ hδ y, h0, zero_mul]
    rfl
  have h := congrFun (finiteFourier_finiteFourier χ.finiteTestFun_mem) (-1)
  rw [hF, finiteFourier_zero, neg_neg, χ.finiteTestFun_one] at h
  exact zero_ne_one h

end HeckeCharacter

end

end GroundTheory.Global
