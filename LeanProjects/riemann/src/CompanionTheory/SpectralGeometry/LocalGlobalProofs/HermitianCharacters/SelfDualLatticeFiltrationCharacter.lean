import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors

namespace GlobalTheory.CompanionTheory.AdeleCharLocal

section

theorem exists_eq_exp (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(ℝ, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : ℝ →+ ℝ := AddMonoidHom.mk' L hLa
  refine ⟨L 1 / (2 * Real.pi), fun t => ?_⟩
  have h3 : L t = t * L 1 := by
    have := map_real_smul l L.continuous t 1
    simpa [l] using this
  have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h4, Circle.coe_exp, h3]
  congr 1
  push_cast
  field_simp

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (x x' : Ainf F) (y y' : Af F) :
    pairA F (x + x') (y + y') = pairA F x y + pairA F x' y' := rfl

theorem algebraMap_eq_pairA (x : F) :
    algebraMap F (AF F) x = pairA F (algebraMap F _ x) 0 + pairA F 0 (algebraMap F _ x) := by
  rw [← pairA_add, add_zero, zero_add]
  rfl

theorem denseRange_fin : DenseRange (algebraMap F (Af F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : Af F => y - z := continuous_const.sub continuous_id
  have hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨y - N • β, hNU β hβ, a, ?_⟩
  rw [e, add_sub_cancel_right]

theorem ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  have h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const))
      (funext h)
  have h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z) :=
    denseRange_fin.equalizer
      (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id))
      (funext fun a => by
        have e := hr a
        have e' := hr' a
        rw [algebraMap_eq_pairA, ha, h] at e
        rw [algebraMap_eq_pairA, ha'] at e'
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))
  have e : x = pairA F x.1 0 + pairA F 0 x.2 := by
    rw [← pairA_add, add_zero, zero_add]
    rfl
  rw [e, ha, ha', congrFun h1, congrFun h2]

theorem ker_mem_nhds {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) : {a : Af F | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : Af F) := by
  let χ : Af F → Circle := fun a => ⟨ψ (pairA F 0 a), by simpa [Submonoid.unitSphere] using hn _⟩
  have hχ : Continuous χ := (hc.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have h0 : χ 0 = 1 := Subtype.ext ψ.map_zero_eq_one
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : Af F) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, h0, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  have : χ (N • a) = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have h1 := hNV (n • a) fun v => nsmul_mem (ha v) n
    have h2 : χ (N • n • a) = χ (N • a) ^ n := by
      apply Subtype.ext
      show ψ (pairA F 0 (N • n • a)) = ((χ (N • a) ^ n : Circle) : ℂ)
      rw [Circle.coe_pow, smul_comm]
      show _ = ψ (pairA F 0 (N • a)) ^ n
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      exact Prod.ext (smul_zero n).symm rfl
    rwa [Set.mem_preimage, h2] at h1
  exact congrArg Subtype.val this

theorem exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2

theorem trace_mul_ne_zero {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {a : F}
    (h : ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ))) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hψ.2.2.2
  refine hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp)
    hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)

theorem exists_realHom : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  have h : ∀ w : InfinitePlace F, ∃ ρ : ℝ →+* w.Completion, Continuous ρ := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom,
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous⟩
    · exact ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.comp Complex.ofRealHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.comp
          Complex.continuous_ofReal⟩
  choose ρ hρ using h
  exact ⟨Pi.ringHom ρ, continuous_pi hρ⟩

theorem exists_trace {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add, add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add, hadd, hy, hz, map_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]

theorem trace_eq_sum (a : F) :
    ((Algebra.trace ℚ F a : ℚ) : ℝ) = ∑ w : InfinitePlace F, w.mult * (w.embedding a).re := by
  classical
  have e := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := a))
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at e
  rw [e, ← (RingHom.equivRatAlgHom (R := F) (S := ℂ)).sum_comp,
    ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      ((RingHom.equivRatAlgHom (R := F) (S := ℂ)) φ a).re = (w.embedding a).re := by
    intro φ hφ
    have h1 : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
      rw [InfinitePlace.mk_embedding]; simpa using hφ
    rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
    · rw [← h2]; rfl
    · rw [← h2]; simp [RingHom.equivRatAlgHom]
  rw [Finset.sum_congr rfl this, Finset.sum_const, InfinitePlace.card_filter_mk_eq]
  simp

theorem exists_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (w : InfinitePlace F) :
    ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_trace hψ
  have ha0 := trace_mul_ne_zero hψ ha
  let T : Ainf F → ℝ := fun z => ∑ u : InfinitePlace F,
    u.mult * (u.embedding a * InfinitePlace.Completion.extensionEmbedding u (z u)).re
  have hT : Continuous T := continuous_finset_sum _ fun u _ => continuous_const.mul
    (Complex.continuous_re.comp (continuous_const.mul
      ((InfinitePlace.Completion.isometry_extensionEmbedding u).continuous.comp (continuous_apply u))))
  have hemb : ∀ (u : InfinitePlace F) (x : F),
      InfinitePlace.Completion.extensionEmbedding u (algebraMap F u.Completion x) = u.embedding x :=
    fun u x => InfinitePlace.Completion.extensionEmbedding_coe u _
  have h1 : (fun z => ψ (pairA F z 0)) =
      fun z => Complex.exp (2 * Real.pi * Complex.I * ((T z : ℝ) : ℂ)) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hψ.1.comp (continuous_id.prodMk continuous_const))
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hT)))
      (funext fun x => by
        have e : T (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F (a * x) : ℚ) : ℝ) := by
          rw [trace_eq_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [map_mul, ← hemb u x]
          rfl
        simp only [Function.comp_apply, ha, e, Complex.ofReal_ratCast])
  have hm : (w.mult : F) ≠ 0 := Nat.cast_ne_zero.2 w.mult_ne_zero
  let z : Ainf F := Pi.single (M := fun u : InfinitePlace F => u.Completion) w
    (algebraMap F _ (a * 2 * w.mult)⁻¹)
  have hz : ∀ w', w' ≠ w → z w' = 0 := fun w' h => Pi.single_eq_of_ne h _
  refine ⟨z, hz, ?_⟩
  have e : T z = 1 / 2 := by
    have hzw : z w = algebraMap F _ (a * 2 * w.mult)⁻¹ := Pi.single_eq_same _ _
    have hm' : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.2 w.mult_ne_zero
    have e2 : a * (a * 2 * w.mult)⁻¹ = (((2 * w.mult : ℚ)⁻¹ : ℚ) : F) := by
      push_cast
      field_simp
    simp only [T]
    rw [Finset.sum_eq_single w (fun u _ hu => by simp [hz u hu]) (by simp), hzw, hemb, ← map_mul, e2,
      map_ratCast, Complex.ratCast_re]
    push_cast
    field_simp
  have e3 : 2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [psiInf, congrFun h1 z, e, e3, Complex.exp_pi_mul_I]
  norm_num

open Classical in

theorem continuous_singleV (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem exists_mem_only (v : HeightOneSpectrum (𝓞 F)) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ t ∈ v.asIdeal ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → t ∉ w.asIdeal := by
  classical
  let P : (Ideal (𝓞 F))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : ClassGroup.mk0 (P ^ Fintype.card (ClassGroup (𝓞 F))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨t, ht⟩ := (ClassGroup.mk0_eq_one_iff (P ^ Fintype.card (ClassGroup (𝓞 F))).2).1 h1
  have ht' : v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) = Ideal.span {t} := ht
  refine ⟨t, ?_, ?_, fun w hw hm => hw ?_⟩
  · rintro rfl
    exact pow_ne_zero _ v.ne_bot (by rw [ht']; simp)
  · exact Ideal.pow_le_self Fintype.card_ne_zero (ht' ▸ Ideal.mem_span_singleton_self t)
  · have h2 : v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) ≤ w.asIdeal := by
      rw [ht', Ideal.span_singleton_le_iff_mem]; exact hm
    have h3 := w.isPrime.le_of_pow_le h2
    exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h3).symm

theorem exists_fin {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := exists_trace hψ
  have ha0 := trace_mul_ne_zero hψ ha
  obtain ⟨N, hN, hNU⟩ :=
    GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (ker_mem_nhds hψ.1 hψ.2.1)
  obtain ⟨t, ht0, htv, htw⟩ := exists_mem_only v
  have key : ∀ y : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F y ≤ 1) →
      ∃ n : ℤ, Algebra.trace ℚ F (a * (N * y)) = n := fun y hy => by
    let β : Af F := algebraMap F (Af F) y - singleV F v (algebraMap F (Fv F v) y)
    have hβ : ∀ w, β w ∈ w.adicCompletionIntegers F := fun w => by
      have e : β w = algebraMap F (Fv F w) y -
        Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
          (algebraMap F (Fv F v) y) w := rfl
      rw [e]
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same, sub_self]
        exact zero_mem _
      · rw [Pi.single_eq_of_ne hw, sub_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
        exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y).trans_le (hy w hw)
    have h1 : ψ (pairA F 0 (N • β)) = 1 := hNU _ hβ
    have h2 : ψ (N • pairA F 0 (singleV F v (algebraMap F (Fv F v) y))) = 1 := by
      rw [AddChar.map_nsmul_eq_pow]
      exact (congrArg (· ^ N) (h _)).trans (one_pow N)
    have h3 : pairA F 0 (algebraMap F (Af F) (N * y)) =
        pairA F 0 (N • β) + N • pairA F 0 (singleV F v (algebraMap F (Fv F v) y)) := by
      refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = 0 + N • 0
        simp
      · change algebraMap F (Af F) (N * y) = N • β + N • singleV F v (algebraMap F (Fv F v) y)
        rw [← nsmul_add, sub_add_cancel, map_mul, map_natCast, nsmul_eq_mul]
    have h4 := hψ.2.2.1 (N * y)
    rw [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h3, AddChar.map_add_eq_mul, h1, h2, mul_one, mul_one,
      ha, Complex.exp_eq_one_iff] at h4
    obtain ⟨n, hn⟩ := h4
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    exact ⟨n, by exact_mod_cast hn⟩
  let D := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    first
      | exact one_ne_zero
      | exact FractionalIdeal.one_ne_zero
      | simp
      | (rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot)
      | (rw [← Ideal.one_eq_top, FractionalIdeal.coeIdeal_one]; simp)
  have hD : ∀ k : ℕ, a * N / (t : F) ^ k ∈ D := fun k => by
    rw [FractionalIdeal.mem_dual h1]
    intro x hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    obtain ⟨n, hn⟩ := key (algebraMap (𝓞 F) F r / (t : F) ^ k) fun w hw => by
      have e : w.valuation F (t : F) = 1 :=
        le_antisymm (w.valuation_le_one t)
          (not_lt.1 fun hl => htw w hw ((w.valuation_lt_one_iff_mem t).1 hl))
      rw [map_div₀, map_pow, e, one_pow, div_one]
      exact w.valuation_le_one r
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hn]
    congr 1
    ring
  obtain ⟨d, hd, hdD⟩ := D.isFractional
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  have hc : v.valuation F (algebraMap (𝓞 F) F d * (a * N)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (mul_ne_zero hd0 (mul_ne_zero ha0 (Nat.cast_ne_zero.2 hN.ne')))
  have htl : v.valuation F (t : F) < 1 := (v.valuation_lt_one_iff_mem t).2 htv
  obtain ⟨k, hk⟩ := exists_pow_lt₀ htl (Units.mk0 _ hc)
  obtain ⟨s, hs⟩ := hdD _ (hD k)
  have ht0' : (t : F) ≠ 0 := by simpa using ht0
  have e : algebraMap (𝓞 F) F d * (a * N) = algebraMap (𝓞 F) F s * (t : F) ^ k := by
    rw [hs, Algebra.smul_def]
    field_simp
  rw [Units.val_mk0, e, map_mul, map_pow] at hk
  exact absurd hk (not_lt.2 (mul_le_of_le_one_left' (v.valuation_le_one s)))

end

theorem char_nontrivial_at_every_place : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiV F ψ v) ∧ ∃ y, psiV F ψ v y ≠ 1) ∧ Continuous (psiInf F ψ) ∧ ∀ (w : InfinitePlace F), ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  intro F _ _ ψ hψ
  exact ⟨fun v => ⟨hψ.1.comp (continuous_const.prodMk (continuous_singleV v)), exists_fin hψ v⟩,
    hψ.1.comp (continuous_id.prodMk continuous_const), fun w => exists_inf hψ w⟩

end GlobalTheory.CompanionTheory.AdeleCharLocal
