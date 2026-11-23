import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesAboveAndNontrivialAbs
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr

noncomputable section

namespace GlobalTheory.TateUnr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liesOver_of_under {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) :
    w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩

theorem absNorm_eq_pow {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  haveI := liesOver_of_under h
  haveI := w.isMaximal
  haveI := v.isMaximal
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal, map_pow]

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {n : ℕ} (h1 : x ≤ WithZero.exp (-(n : ℤ)))
    (h2 : ¬ x ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) : x = WithZero.exp (-(n : ℤ)) := by
  have hx : x ≠ 0 := fun h => h2 (h ▸ zero_le)
  rw [← WithZero.exp_log hx] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h2
  omega

theorem intValuation_intNorm {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (a : 𝓞 E) (ha : a ∈ w.asIdeal) (ha2 : a ∉ w.asIdeal ^ 2)
    (hao : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = v → w' ≠ w → a ∉ w'.asIdeal) :
    v.intValuation (Algebra.intNorm (𝓞 F) (𝓞 E) a) = WithZero.exp (-(w.asIdeal.inertiaDeg (𝓞 F) : ℤ)) := by
  classical
  haveI := liesOver_of_under h
  haveI := w.isMaximal
  haveI := v.isMaximal
  set f := w.asIdeal.inertiaDeg (𝓞 F)
  obtain ⟨J, hJ⟩ : w.asIdeal ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have hspan : Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) a} = v.asIdeal ^ f * Ideal.relNorm (𝓞 F) J := by
    rw [← Ideal.relNorm_singleton, hJ, map_mul, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal]
  have hJw : ¬ J ≤ w.asIdeal := fun hle => ha2 (by
    have : Ideal.span {a} ≤ w.asIdeal ^ 2 := by rw [hJ, sq]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this)
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact ha2 (hJ ▸ zero_mem _)
  have hnot : ¬ Ideal.relNorm (𝓞 F) J ≤ v.asIdeal := by
    intro hle
    rw [← Ideal.prod_normalizedFactors_eq_self hJ0, map_multiset_prod] at hle
    obtain ⟨Q, hQ, hQle⟩ := (Ideal.IsPrime.multiset_prod_map_le _ v.isPrime).1 hle
    have hQ0 : Q ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hQ
    have hQ' := (Ideal.mem_normalizedFactors_iff hJ0).1 hQ
    haveI : Q.IsPrime := hQ'.1
    haveI : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 hQ'.1
    rw [Ideal.relNorm_eq_pow_of_isMaximal Q (Q.under (𝓞 F))] at hQle
    have hPv : Q.under (𝓞 F) = v.asIdeal :=
      (inferInstance : (Q.under (𝓞 F)).IsMaximal).eq_of_le v.isPrime.ne_top (v.isPrime.le_of_pow_le hQle)
    let w' : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ'.1, hQ0⟩
    have hw' : w'.under (𝓞 F) = v := HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact hPv)
    by_cases hne : w' = w
    · exact hJw (by rw [← hne]; exact hQ'.2)
    · refine hao w' hw' hne ?_
      have : Ideal.span {a} ≤ Q := by rw [hJ]; exact (Ideal.mul_le_inf.trans inf_le_right).trans hQ'.2
      exact (Ideal.span_singleton_le_iff_mem _).1 this
  refine eq_exp_of_le ((HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 ?_) ?_
  · have : Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) a} ≤ v.asIdeal ^ f := by
      rw [hspan]; exact Ideal.mul_le_inf.trans inf_le_left
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  · rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    intro hmem
    have hle : Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) a} ≤ v.asIdeal ^ (f + 1) :=
      (Ideal.span_singleton_le_iff_mem _).2 hmem
    rw [hspan, ← Ideal.dvd_iff_le, pow_succ] at hle
    have hv0 : v.asIdeal ^ f ≠ 0 := pow_ne_zero _ v.ne_bot
    exact hnot (Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hv0).1 hle))

end GlobalTheory.TateUnr

namespace GlobalTheory.TateUnr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_sep_two (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ a : 𝓞 E, a ∈ w.asIdeal ∧ a ∉ w.asIdeal ^ 2 ∧
      ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = v → w' ≠ w → a ∉ w'.asIdeal := by
  classical
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ w.asIdeal, π ∉ w.asIdeal ^ 2 := by
    have := Ideal.pow_right_strictAnti w.asIdeal w.ne_bot w.isPrime.ne_top (show 1 < 2 by norm_num)
    simp only [pow_one] at this
    obtain ⟨π, h1, h2⟩ := Set.exists_of_ssubset this
    exact ⟨π, h1, h2⟩
  let s : Finset (HeightOneSpectrum (𝓞 E)) := insert w (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun i => i.asIdeal)
    (fun i => if i = w then 2 else 1) (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun i => if i.1 = w then π else 1)
  have hw := hy w (Finset.mem_insert_self _ _)
  simp only [if_pos rfl] at hw
  have hyw : y ∈ w.asIdeal := by
    have := Ideal.pow_le_self two_ne_zero hw
    simpa using w.asIdeal.add_mem this hπ
  refine ⟨y, hyw, fun hy2 => hπ2 ?_, fun w' hw' hne hyw' => ?_⟩
  · have := (w.asIdeal ^ 2).sub_mem hy2 hw
    simpa using this
  · have h' := hy w' (Finset.mem_insert_of_mem ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 hw'))
    simp only [if_neg hne, pow_one] at h'
    exact w'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w'.asIdeal.sub_mem hyw' h'))

theorem valued_eq_exp_neg_one (w : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) (ha : a ∈ w.asIdeal)
    (ha2 : a ∉ w.asIdeal ^ 2) : Valued.v (algebraMap E (w.adicCompletion E) (a : E)) = WithZero.exp (-1) := by
  show Valued.v (((a : E)) : w.adicCompletion E) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have := eq_exp_of_le (n := 1) ((HeightOneSpectrum.intValuation_le_pow_iff_mem w a 1).2 (by rw [pow_one]; exact ha))
    (by rw [HeightOneSpectrum.intValuation_le_pow_iff_mem w a (1 + 1)]; exact ha2)
  simpa using this

theorem norm_intNorm {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (a : 𝓞 E) (ha : a ∈ w.asIdeal) (ha2 : a ∉ w.asIdeal ^ 2)
    (hao : ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = v → w' ≠ w → a ∉ w'.asIdeal) :
    ‖algebraMap F (Fv F v) ((Algebra.intNorm (𝓞 F) (𝓞 E) a : 𝓞 F) : F)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  have e : ‖algebraMap F (Fv F v) ((Algebra.intNorm (𝓞 F) (𝓞 E) a : 𝓞 F) : F)‖ =
      ‖FinitePlace.embedding v ((Algebra.intNorm (𝓞 F) (𝓞 E) a : 𝓞 F) : F)‖ := rfl
  rw [e, FinitePlace.norm_embedding', HeightOneSpectrum.valuation_of_algebraMap, intValuation_intNorm h a ha ha2 hao,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, absNorm_eq_pow h]
  have t : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := -(w.asIdeal.inertiaDeg (𝓞 F) : ℤ)))) =
      -(w.asIdeal.inertiaDeg (𝓞 F) : ℤ) := rfl
  rw [t, NNReal.coe_zpow, zpow_neg, zpow_natCast]
  push_cast
  rfl

end GlobalTheory.TateUnr

namespace GlobalTheory.TateUnr

open GlobalTheory.PlaceAbove (absE_locIdele_of_unit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_unif_absE (w : HeightOneSpectrum (𝓞 E)) :
    ∃ α : (w.adicCompletion E)ˣ, Valued.v (α : w.adicCompletion E) = WithZero.exp (-1) ∧
      ((absE F E (locIdele F w α) : ℝ≥0) : ℝ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  classical
  obtain ⟨a, haw, ha2, hao⟩ := exists_sep_two (F := F) (w.under (𝓞 F)) w
  have hE0 : (a : E) ≠ 0 := fun h => ha2 (by rw [show a = 0 by exact_mod_cast h]; exact zero_mem _)
  let y : (Fv F (w.under (𝓞 F)) ⊗[F] E)ˣ :=
    Units.map (inclR (F := F) (Fv F (w.under (𝓞 F)))).toMonoidHom (Units.mk0 (a : E) hE0)
  have hval : ∀ (w' : HeightOneSpectrum (𝓞 E)) (h : w'.under (𝓞 F) = w.under (𝓞 F)),
      ((Units.map (toCompl h).toMonoidHom y : (w'.adicCompletion E)ˣ) : w'.adicCompletion E) =
        algebraMap E _ (a : E) := by
    intro w' h
    show toCompl h ((1 : Fv F (w.under (𝓞 F))) ⊗ₜ[F] (a : E)) = _
    rw [toCompl_tmul, map_one, one_mul]
  have key := congrArg (absE F E) (GlobalTheory.LFun.ideleAt_eq_prod_locIdele (w.under (𝓞 F)) y)
  rw [GlobalTheory.Doubling.absE_ideleAt, map_prod] at key
  have hmem : w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F (w.under (𝓞 F))).toFinset :=
    (Formalism.L2.Host.finite_aboveF (L := E) F (w.under (𝓞 F))).mem_toFinset.2 rfl
  rw [Finset.prod_eq_single_of_mem ⟨w, hmem⟩ (Finset.mem_attach _ _) (fun b _ hb => by
    have hbv : b.1.under (𝓞 F) = w.under (𝓞 F) :=
      (Formalism.L2.Host.finite_aboveF (L := E) F (w.under (𝓞 F))).mem_toFinset.1 b.2
    have hne : b.1 ≠ w := fun e => hb (Subtype.ext e)
    have hv1 := GlobalTheory.PlaceAbove.valued_eq_one b.1 a (hao b.1 hbv hne)
    refine absE_locIdele_of_unit b.1 _ ?_ ?_
    · rw [hval]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv1.le
    · rw [Units.val_inv_eq_inv_val, hval]
      refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [map_inv₀, hv1, inv_one])] at key
  refine ⟨Units.map (toCompl (rfl : w.under (𝓞 F) = w.under (𝓞 F))).toMonoidHom y, ?_, ?_⟩
  · rw [hval]
    exact valued_eq_exp_neg_one w a haw ha2
  · have key' : absE F E (locIdele F w (Units.map (toCompl (rfl : w.under (𝓞 F) = w.under (𝓞 F))).toMonoidHom y)) =
        GlobalTheory.Doubling.absEv F E (w.under (𝓞 F)) y := key.symm
    rw [key', GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
    show ‖Algebra.norm (Fv F (w.under (𝓞 F))) (inclR (F := F) (Fv F (w.under (𝓞 F))) (a : E))‖ = _
    rw [GlobalTheory.Doubling.norm_inclR, ← Algebra.algebraMap_intNorm (L := E) (A := 𝓞 F) (B := 𝓞 E) a]
    exact norm_intNorm rfl a haw ha2 hao

theorem absE_locIdele_eq_zpow (w : HeightOneSpectrum (𝓞 E)) (α x : (w.adicCompletion E)ˣ)
    (hα : Valued.v (α : w.adicCompletion E) = WithZero.exp (-1)) :
    absE F E (locIdele F w x) =
      absE F E (locIdele F w α) ^ (-WithZero.log (Valued.v (x : w.adicCompletion E))) := by
  set n := -WithZero.log (Valued.v (x : w.adicCompletion E)) with hn
  have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  have h0 : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n) := by rw [hn, neg_neg, WithZero.exp_log hx0]
  have hu : Valued.v ((x * α ^ (-n) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hα, h0, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 : absE F E (locIdele F w (x * α ^ (-n))) = 1 := by
    refine absE_locIdele_of_unit w _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le) ?_
    rw [Units.val_inv_eq_inv_val]
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [map_inv₀, hu, inv_one]
  have hc : absE F E (locIdele F w α) ≠ 0 := by
    intro h
    have := congrArg (absE F E) (congrArg (locIdele F w) (mul_inv_cancel α))
    rw [map_mul, map_mul, h, zero_mul, map_one, map_one] at this
    exact zero_ne_one this
  have hinv : ∀ a : (w.adicCompletion E)ˣ,
      ((absE F E).comp (locIdele F w)) a⁻¹ = (((absE F E).comp (locIdele F w)) a)⁻¹ :=
    fun a => eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have h2 : ((absE F E).comp (locIdele F w)) (x * α ^ (-n)) = 1 := h1
  have hc' : ((absE F E).comp (locIdele F w)) α ≠ 0 := hc
  rw [map_mul, map_zpow' _ hinv, zpow_neg] at h2
  exact (mul_inv_eq_one₀ (zpow_ne_zero n hc')).1 h2

theorem absE_idelesAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (l : idelesAt E (evFin F v)),
    ((absE F E l.1 : ℝ≥0) : ℝ) = ∏ w : aboveF (L := E) F v, ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) ^ (-ordV v l w) := by
  intro F E _ _ _ _ _ v l
  have h1 : absE F E l.1 = ∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach,
      absE F E (locIdele F w.1 (compW ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2) l)) := by
    conv_lhs => rw [← ideleAt_unitFin l.2]
    rw [GlobalTheory.LFun.ideleAt_eq_prod_locIdele, map_prod]
    rfl
  rw [h1, NNReal.coe_prod, Finset.prod_coe_sort_eq_attach]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨α, hα, hc⟩ := exists_unif_absE (F := F) w.1
  rw [absE_locIdele_eq_zpow w.1 α _ hα, NNReal.coe_zpow, hc, inv_zpow']
  rfl

end GlobalTheory.TateUnr
