import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdeleCharConductor

theorem exists_freq {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℂ) (hf : Continuous f) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) (hn : ∀ x, ‖f x‖ = 1) :
    ∃ lam : ι → ℝ, ∀ y, f y = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lam v * y v : ℝ) : ℂ)) := by
  classical
  have hne : ∀ x, f x ≠ 0 := fun x h => by simpa [h] using hn x
  let g : C(ι → ℝ, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨f z, hne z⟩, hf.subtype_mk _⟩
  obtain ⟨G, ⟨hG0, hG⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 0
    (Subtype.ext (by simp [g, h0]))
  have hG' : ∀ z, Complex.exp (G z) = f z := fun z => congrArg Subtype.val (congrFun hG z)
  have hGadd : ∀ x y, G (x + y) = G x + G y := by
    intro x y
    have hc : Continuous fun y => G (x + y) - G y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hG', hadd]
      rw [mul_div_assoc, mul_div_assoc, div_self (hne _), div_self (hne _)])) y 0
    simp only [add_zero, hG0, sub_zero] at this
    rw [← this]; ring
  let L : (ι → ℝ) →L[ℝ] ℂ := (AddMonoidHom.mk' G hGadd).toRealLinearMap G.continuous
  have hL : ∀ y, L y = G y := fun _ => rfl
  have hre : ∀ y, (L y).re = 0 := fun y => by
    have := hn y
    rwa [← hG', Complex.norm_exp, Real.exp_eq_one_iff] at this
  refine ⟨fun v => (L (Pi.single v 1)).im / (2 * Real.pi), fun y => ?_⟩
  rw [← hG', ← hL]
  congr 1
  conv_lhs => rw [pi_eq_sum_univ' y, map_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : L (Pi.single v 1) = ((L (Pi.single v 1)).im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im (L (Pi.single v 1)), hre]
    simp
  rw [map_smul, Complex.real_smul]
  conv_lhs => rw [e]
  field_simp

variable {F : Type} [Field F] [NumberField F]

theorem exists_psiInf_ne_one {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) : ∃ x, psiInf F ψ x ≠ 1 := by
  by_contra hn
  push Not at hn
  have hrat : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 := fun x => by
    rw [GlobalTheory.StdRat.char_fin_rat ψ h, hn]
  have hp : Continuous fun y : Af F => pairA F 0 y := Continuous.prodMk continuous_const continuous_id
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = 1 :=
    fun α hα => GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 y) = 1})
      (isClosed_eq (h.1.comp hp) continuous_const) (fun a => hrat a) α hα
  have hfin : ∀ y : Af F, ψ (pairA F 0 y) = 1 := fun y => by
    obtain ⟨a, s, hs, hy⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos y
    have e1 : pairA F 0 y = pairA F 0 (algebraMap F (Af F) a) + pairA F 0 s := by
      refine Prod.ext (add_zero _).symm ?_
      show y = algebraMap F (Af F) a + s
      simpa only [one_smul] using hy
    rw [e1, AddChar.map_add_eq_mul, hrat, hint s hs, one_mul]
  obtain ⟨a, ha⟩ := h.2.2.2
  apply ha
  have e2 : a = pairA F a.1 0 + pairA F 0 a.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [e2, AddChar.map_add_eq_mul, hfin, mul_one]
  exact hn a.1

theorem exists_psiInf_eq [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) :
    ∃ lam : InfinitePlace F → ℝ, ∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w, lam w * (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)) := by
  let g : (InfinitePlace F → ℝ) → Ainf F := fun y w =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w)
  have hg : Continuous g := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
      (continuous_apply w)
  have hp : Continuous fun y : Ainf F => pairA F y 0 := Continuous.prodMk continuous_id continuous_const
  obtain ⟨lam, hlam⟩ := exists_freq (fun y => psiInf F ψ (g y)) ((h.1.comp hp).comp hg)
    (by
      have : g 0 = 0 := funext fun w => map_zero _
      show ψ (pairA F (g 0) 0) = 1
      rw [this]
      exact ψ.map_zero_eq_one)
    (fun x y => by
      have : g (x + y) = g x + g y := funext fun w => map_add _ _ _
      show ψ (pairA F (g (x + y)) 0) = ψ _ * ψ _
      rw [this, ← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext rfl (add_zero _).symm))
    (fun x => h.2.1 _)
  refine ⟨lam, fun x => ?_⟩
  rw [← hlam]
  congr 1
  funext w
  show x w = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm _
  rw [RingEquiv.eq_symm_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact (Complex.ofReal_re _).symm.trans (congrArg Complex.re
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) (x w)))

theorem embedding_re [IsTotallyReal F] (w : InfinitePlace F) (x : F) :
    (((w.embedding x).re : ℝ) : ℂ) = w.embedding x :=
  Complex.conj_eq_iff_re.1 (RingHom.congr_fun (InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)) x)

theorem exists_eq_embedding [IsTotallyReal F] (lam : InfinitePlace F → ℝ)
    (h : ∀ r : 𝓞 F, ∃ q : ℚ, ∑ w, lam w * (w.embedding (r : F)).re = q) :
    ∃ a : F, ∀ w, lam w = (w.embedding a).re := by
  choose q hq using h
  let T : F →ₗ[ℚ] ℝ := AddMonoidHom.toRatLinearMap (AddMonoidHom.mk' (fun x => ∑ w, lam w * (w.embedding x).re)
    fun x y => by simp only [map_add, Complex.add_re, mul_add, Finset.sum_add_distrib])
  let l : F →ₗ[ℚ] ℚ := (integralBasis F).constr ℚ fun i => q (RingOfIntegers.basis F i)
  have hT : T = (Algebra.linearMap ℚ ℝ).comp l := (integralBasis F).ext fun i => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, integralBasis_apply]
    exact hq _
  let a : F := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm l
  have ha : ∀ x, Algebra.trace ℚ F (a * x) = l x := fun x =>
    LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm ℚ F) l x
  have hli : LinearIndependent ℂ fun w : InfinitePlace F => ((w.embedding : F →* ℂ) : F → ℂ) :=
    (linearIndependent_monoidHom F ℂ).comp (fun w : InfinitePlace F => (w.embedding : F →* ℂ)) fun v w hvw => by
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w]
      exact congrArg InfinitePlace.mk (RingHom.ext fun x => DFunLike.congr_fun hvw x)
  have key := Fintype.linearIndependent_iff.1 hli (fun w => (lam w : ℂ) - w.embedding a) (by
    funext x
    have h1 : (∑ w, lam w * (w.embedding x).re : ℝ) = ((l x : ℚ) : ℝ) := LinearMap.congr_fun hT x
    have h2 := GlobalTheory.SnMass.Inhab.sum_places_eq_trace (a * x)
    have h3 := congrArg Complex.ofReal h1
    rw [ha] at h2
    push_cast at h2 h3
    simp only [embedding_re] at h2 h3
    simp only [map_mul] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, MonoidHom.coe_coe, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    rw [h2, h3, sub_self])
  refine ⟨a, fun w => ?_⟩
  have := congrArg Complex.re (sub_eq_zero.1 (key w))
  rwa [Complex.ofReal_re] at this

theorem extensionEmbedding_algebraMap (w : InfinitePlace F) (x : F) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap F (Ainf F) x w) = w.embedding x :=
  InfinitePlace.Completion.extensionEmbedding_coe w _

theorem exists_scaling [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) :
    ∃ a : F, a ≠ 0 ∧ ∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (w.embedding a).re *
        (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)) := by
  obtain ⟨lam, hlam⟩ := exists_psiInf_eq h
  obtain ⟨N, hN, hU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.eventually_fin_eq_one h)
  obtain ⟨a, ha⟩ := exists_eq_embedding lam fun r => by
    have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) (r : F))) = 1 :=
      hU _ ((GlobalTheory.SnMass.Inhab.integral_iff _).2 ⟨r, rfl⟩)
    rw [← map_nsmul, GlobalTheory.StdRat.char_fin_rat ψ h, hlam, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    simp only [extensionEmbedding_algebraMap] at hn
    simp only [map_neg, map_nsmul, Complex.neg_re, Complex.re_nsmul] at hn
    simp only [nsmul_eq_mul, mul_neg, Finset.sum_neg_distrib, mul_left_comm _ (N : ℝ), ← Finset.mul_sum] at hn
    have hn' : -((N : ℝ) * ∑ w, lam w * (w.embedding (r : F)).re) = n := by exact_mod_cast hn
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨-n / N, ?_⟩
    push_cast
    rw [← hn']
    field_simp
  refine ⟨a, ?_, fun x => by simp only [hlam, ha]⟩
  rintro rfl
  obtain ⟨x, hx⟩ := exists_psiInf_ne_one h
  apply hx
  simp [hlam, ha]

theorem conductor_of_scaling [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) {a : F} (ha : a ≠ 0)
    (hinf : ∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (w.embedding a).re *
        (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)))
    (u : HeightOneSpectrum (𝓞 F)) (t : Fv F u) :
    (∀ s ∈ u.adicCompletionIntegers F, psiV F ψ u (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp
      (FractionalIdeal.count F u (FractionalIdeal.spanSingleton (𝓞 F)⁰ a * (differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)))) := by
  let ψ' : AddChar (AF F) ℂ := ψ.mulShift (algebraMap F (AF F) a⁻¹)
  have h' : IsCharAF F ψ' := by
    refine ⟨h.1.comp (continuous_const.mul continuous_id), fun x => h.2.1 _, fun b => ?_, ?_⟩
    · rw [AddChar.mulShift_apply, ← map_mul]; exact h.2.2.1 _
    · obtain ⟨x, hx⟩ := h.2.2.2
      refine ⟨algebraMap F (AF F) a * x, ?_⟩
      rwa [AddChar.mulShift_apply, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  have hs := GlobalTheory.SnMass.Inhab.stdAt_of_psiInf h' (fun b => by
    have e : psiInf F ψ' (algebraMap F (Ainf F) b) = psiInf F ψ (algebraMap F (Ainf F) (a⁻¹ * b)) := by
      rw [map_mul]
      exact congrArg ψ (Prod.ext rfl (mul_zero _))
    rw [e, hinf, ← GlobalTheory.SnMass.Inhab.sum_places_eq_trace]
    simp only [extensionEmbedding_algebraMap]
    rw [Complex.ofReal_sum, Complex.ofReal_sum]
    congr 2
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Complex.ofReal_mul, embedding_re, embedding_re, embedding_re, ← map_mul,
      mul_inv_cancel_left₀ ha]) u (algebraMap F (Fv F u) a * t)
  have e : ∀ s, psiV F ψ' u (algebraMap F (Fv F u) a * t * s) = psiV F ψ u (t * s) := fun s => by
    refine congrArg ψ (Prod.ext (mul_zero _) ?_)
    show algebraMap F (Af F) a⁻¹ * singleV F u _ = singleV F u _
    rw [mul_comm, GlobalTheory.SnMass.Inhab.single_mul]
    congr 1
    show _ * algebraMap F (Fv F u) a⁻¹ = _
    have : algebraMap F (Fv F u) a ≠ 0 := by simpa using ha
    rw [map_inv₀]
    field_simp
  simp only [e] at hs
  rw [hs]
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
  rw [FractionalIdeal.count_mul F u (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha) hD]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, GlobalTheory.Idele.valued_algebraMap,
    GlobalTheory.Idele.valuation_eq_exp_neg_count u ha]
  set i := FractionalIdeal.count F u (FractionalIdeal.spanSingleton (𝓞 F)⁰ a)
  set j := FractionalIdeal.count F u ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have key : WithZero.exp (-i) * Valued.v t * WithZero.exp (-j) ≤ 1 ↔ Valued.v t ≤ WithZero.exp (i + j) := by
    rw [mul_right_comm, ← WithZero.exp_add, ← neg_add, WithZero.exp_neg, inv_mul_le_one₀ WithZero.exp_pos]
  rw [← key]
  constructor
  · intro H
    obtain ⟨y, hy, hy'⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hD u
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [← hy']
    exact H d hd
  · intro H d hd
    refine le_trans ?_ H
    gcongr
    exact (GlobalTheory.Idele.mem_iff_valuation_le hD _).1 (FractionalIdeal.mem_coeIdeal_of_mem _ hd) u

theorem finprod_absNorm_zpow_count {I : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) :
    ∏ᶠ u : HeightOneSpectrum (𝓞 F), (Ideal.absNorm u.asIdeal : ℝ) ^ FractionalIdeal.count F u I =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  let g : FractionalIdeal (𝓞 F)⁰ F →*₀ ℝ := (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  have hg : ∀ J, g J = ((FractionalIdeal.absNorm J : ℚ) : ℝ) := fun _ => rfl
  conv_rhs => rw [← hg, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI]
  rw [map_finprod g]
  · refine finprod_congr fun u => ?_
    rw [map_zpow₀, hg, FractionalIdeal.coeIdeal_absNorm]
    simp
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun u hu h0 => hu ?_
    simp only [h0, zpow_zero]

open MeasureTheory Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean in

theorem real_part_and_conductors : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ ψ : AddChar (AF I.F) ℂ, IsCharAF I.F ψ → ∃ (lamv : InfinitePlace I.F → ℝ) (m : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) → ℤ), (∀ v, lamv v ≠ 0) ∧ (∀ x, psiInf I.F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) ∧ (Function.support m).Finite ∧ (∀ u (t : Fv I.F u), (∀ s ∈ u.adicCompletionIntegers I.F, psiV I.F ψ u (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp (m u)) ∧ ∏ᶠ u, (Ideal.absNorm u.asIdeal : ℝ) ^ m u = |(discr I.F : ℝ)| * ∏ v, |lamv v| := by
  intro I θ hθ ψ hψ
  haveI := I.cm.totReal
  obtain ⟨a, ha, hinf⟩ := exists_scaling hψ
  have hθ' : ∀ v x, θ v (x ⊗ₜ[I.F] (1 : I.E)) = InfinitePlace.Completion.extensionEmbedding v (x v) := fun v =>
    congrFun ((InfiniteAdeleRing.denseRange_algebraMap I.F).equalizer (hθ v).2
      ((InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v))
      (funext fun x => by
        show θ v (algebraMap I.F (Ainf I.F) x ⊗ₜ[I.F] (1 : I.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, (hθ v).1, I.φ_over]
        exact (extensionEmbedding_algebraMap v x).symm))
  have hD : ((differentIdeal ℤ (𝓞 I.F) : Ideal (𝓞 I.F)) : FractionalIdeal (𝓞 I.F)⁰ I.F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
  refine ⟨fun v => (v.embedding a).re, _, fun v hv => ?_, fun x => by simp only [hθ', hinf], ?_,
    conductor_of_scaling hψ ha hinf, ?_⟩
  · have := embedding_re v a
    rw [show (v.embedding a).re = 0 from hv, Complex.ofReal_zero, eq_comm, map_eq_zero] at this
    exact ha this
  · exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  · rw [finprod_absNorm_zpow_count (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha) hD), map_mul,
      FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm,
      absNorm_differentIdeal I.F (𝓞 I.F), Rat.cast_mul, ← InfinitePlace.prod_eq_abs_norm, mul_comm]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, ← InfinitePlace.norm_embedding_eq,
        ← embedding_re, Complex.norm_real, Real.norm_eq_abs]

end GlobalTheory.AdeleCharConductor
