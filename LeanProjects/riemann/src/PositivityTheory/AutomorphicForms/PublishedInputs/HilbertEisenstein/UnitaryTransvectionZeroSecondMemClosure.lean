import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.TateTheta
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical FourierTransform
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L2

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_omega_eq_one {ω : HChar F} (h : IsOfFinOrder ω) (x : Ideles F) :
    ‖((ω.1 x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq_one
  have h1 : (ω.1 x) ^ n = 1 := by
    have := congrArg (fun χ : HChar F => (χ.1 x)) hpow
    simpa using this
  have h2 : ((ω.1 x : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 : ‖((ω.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h2, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

theorem finite_support {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, hω⟩ := isOfFinOrder_iff_pow_eq_one.1 hH.fin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => by
    have := congrArg (fun ξ : HChar F => ξ.1 x) hω
    simpa using this
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  exact hw (Nat.le_zero.1 ((hH.cond w).2 fun x hu _ => MonoidHom.mem_ker.1 (key w x hu fun h => absurd h hwS)))

def Nc (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_Nc {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v ((Nc c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c v := by
  refine count_finprod_primeIdealUnit_zpow (fun w => (c w : ℤ)) ?_ v
  refine Filter.eventually_cofinite.2 ((finite_support hH).subset fun w hw => ?_)
  intro h
  exact hw (by simp [h])

def gfin (c : HeightOneSpectrum (𝓞 F) → ℕ) : Af F → ℂ := cosetIndicator (Nc c) 1

def oddPoly (x : mixedSpace F) : ℂ := ∏ w : {w : InfinitePlace F // InfinitePlace.IsReal w}, (Complex.I * ((x.1 w : ℝ) : ℂ))

theorem hasTemperateGrowth_oddPoly : (oddPoly (F := F)).HasTemperateGrowth := by
  refine hasTemperateGrowth_finsetProd _ fun w _ => ?_
  have h := ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w : InfinitePlace F // w.IsReal} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
        ({w : InfinitePlace F // w.IsComplex} → ℂ))) : mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.const Complex.I).mul h

variable (F) in

def oddSchwartz : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ oddPoly
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))

theorem oddSchwartz_apply (x : mixedSpace F) :
    oddSchwartz F x = oddPoly x *
      ((Real.exp (-Real.pi * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [oddSchwartz, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_oddPoly,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

instance isEmpty_complexPlaces : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

theorem pInf_apply_eq (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F x v = (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := by
  rw [homeomorphMixedSpace_apply]; rfl

theorem arch_zero_eq (B : Ad F) :
    arch (UpperTheory.V.TR.pInf F 0) (UpperTheory.V.TR.pInf F B) = oddSchwartz F (homeomorphMixedSpace F B.1) := by
  set m := homeomorphMixedSpace F B.1 with hm
  have hb : ∀ v : InfinitePlace F, UpperTheory.V.TR.pInf F B v = m.1 ⟨v, IsTotallyReal.isReal v⟩ :=
    fun v => pInf_apply_eq B v
  have hc : (∑ w : {w : InfinitePlace F // w.IsComplex}, ‖m.2 w‖ ^ 2) = 0 := by simp
  rw [oddSchwartz_apply, hc, mul_zero, add_zero, Complex.ofReal_exp]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum, oddPoly, ← Finset.prod_mul_distrib]
  unfold arch
  rw [Finset.prod_subtype Finset.univ (p := fun v : InfinitePlace F => v.IsReal)
    (fun v => by simp [IsTotallyReal.isReal v])]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [hb w.1]
  simp only [map_zero, Pi.zero_apply, Complex.ofReal_zero, zero_add, Subtype.coe_eta]
  ring_nf

def f0 (c : HeightOneSpectrum (𝓞 F) → ℕ) (B : Ad F) : ℂ := Phi c ![0, B]

theorem eisensteinFxConstantTerm_rationalIndex_eq {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    f0 c = schwartzBruhatTensor (oddSchwartz F) (gfin c) := by
  funext B
  have hcond : (∀ w, Valued.v (pLoc F w (pFin F ((![0, B] : Fin 2 → Ad F) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((![0, B] : Fin 2 → Ad F) 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) ↔
      B.2 - 1 ∈ idealFiniteAdeles (Nc c) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_idealFiniteAdeles]
    refine forall_congr' fun w => ?_
    rw [count_Nc hH]
    simp only [map_zero, zero_le, true_and]
    rfl
  unfold f0 Phi
  rw [schwartzBruhatTensor, gfin, cosetIndicator_apply]
  have ha : arch (UpperTheory.V.TR.pInf F ((![0, B] : Fin 2 → Ad F) 0)) (UpperTheory.V.TR.pInf F ((![0, B] : Fin 2 → Ad F) 1)) =
      oddSchwartz F (homeomorphMixedSpace F B.1) := arch_zero_eq B
  rw [ha]
  congr 1
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl

theorem unitaryTransvection_zero_second_mem_closure {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) : f0 c ∈ schwartzBruhat F := by
  rw [eisensteinFxConstantTerm_rationalIndex_eq hH]
  exact schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _)

theorem test_function_at_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : f0 c 0 = 0 := by
  have h : arch (UpperTheory.V.TR.pInf F 0) (UpperTheory.V.TR.pInf F 0) = 0 := by
    unfold arch
    refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary (InfinitePlace F))) ?_
    simp
  unfold f0 Phi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h, zero_mul]

theorem integral_oddSchwartz : ∫ x, oddSchwartz F x ∂selfDualMeasure F = 0 := by
  set w₀ : {w : InfinitePlace F // w.IsReal} := ⟨w0 F, IsTotallyReal.isReal _⟩
  set σ₁ : ({w : InfinitePlace F // w.IsReal} → ℝ) → ({w : InfinitePlace F // w.IsReal} → ℝ) :=
    fun a i => (fun i (r : ℝ) => if i = w₀ then -r else r) i (a i) with hσ₁def
  have hσ₁ : MeasurePreserving σ₁ volume volume := by
    refine volume_preserving_pi (ι := {w : InfinitePlace F // w.IsReal})
      (f := fun i (r : ℝ) => if i = w₀ then -r else r) fun i => ?_
    by_cases h : i = w₀
    · have e : (fun r : ℝ => if i = w₀ then -r else r) = Neg.neg := funext fun r => if_pos h
      rw [e]; exact Measure.measurePreserving_neg volume
    · have e : (fun r : ℝ => if i = w₀ then -r else r) = id := funext fun r => if_neg h
      rw [e]; exact MeasurePreserving.id volume
  set σ : mixedSpace F → mixedSpace F := Prod.map σ₁ id with hσdef
  have hσ : MeasurePreserving σ volume volume := by
    rw [Measure.volume_eq_prod]
    exact hσ₁.prod (MeasurePreserving.id volume)
  have hodd : ∀ x, oddSchwartz F (σ x) = - oddSchwartz F x := by
    intro x
    have hsq : ∀ w, (σ x).1 w ^ 2 = x.1 w ^ 2 := fun w => by
      simp only [hσdef, hσ₁def, Prod.map_fst]
      split_ifs <;> simp
    have hg : (∑ w, (σ x).1 w ^ 2 + 2 * ∑ w, ‖(σ x).2 w‖ ^ 2) = (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2) := by
      simp only [hsq]; rfl
    have hp : oddPoly (σ x) = - oddPoly x := by
      unfold oddPoly
      rw [Fintype.prod_eq_mul_prod_compl w₀, Fintype.prod_eq_mul_prod_compl w₀ (fun w => Complex.I * ((x.1 w : ℝ) : ℂ))]
      have hrest : ∏ i ∈ ({w₀}ᶜ : Finset _), Complex.I * (((σ x).1 i : ℝ) : ℂ) =
          ∏ i ∈ ({w₀}ᶜ : Finset _), Complex.I * ((x.1 i : ℝ) : ℂ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have : i ≠ w₀ := by simpa using hi
        simp [hσdef, hσ₁def, this]
      rw [hrest]
      simp [hσdef, hσ₁def]
    rw [oddSchwartz_apply, oddSchwartz_apply, hp, hg, neg_mul]
  have hI : ∫ x, oddSchwartz F x ∂volume = 0 := by
    have h1 : ∫ x, oddSchwartz F x ∂volume = ∫ x, oddSchwartz F (σ x) ∂volume := by
      conv_lhs => rw [← hσ.map_eq]
      exact integral_map hσ.measurable.aemeasurable (oddSchwartz F).continuous.aestronglyMeasurable
    simp only [hodd, integral_neg] at h1
    have h2 : (2 : ℂ) * ∫ x, oddSchwartz F x ∂volume = 0 := by linear_combination h1
    simpa using h2
  rw [selfDualMeasure, integral_smul_measure, hI, smul_zero]

theorem fourier_test_function_at_zero {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    adelicFourier F (f0 c) 0 = 0 := by
  rw [eisensteinFxConstantTerm_rationalIndex_eq hH, adelicFourier_schwartzBruhatTensor]
  simp only [schwartzBruhatTensor, mixedFourierSchwartz_apply]
  have h0 : homeomorphMixedSpace F (0 : Ad F).1 = 0 := by
    rw [homeomorphMixedSpace_apply]; exact map_zero _
  rw [h0, mixedFourier_apply]
  have : (fun x : mixedSpace F => 𝐞 (-mixedTraceForm F x 0) • oddSchwartz F x) = fun x => oddSchwartz F x := by
    funext x
    simp
  rw [this, integral_oddSchwartz, zero_mul]

theorem zeroRow_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) {ω : HChar F} (hH : Hyp ω c) (τ : IdeleGroup F) :
    zeroRow c τ = adelicTheta (f0 c) τ := by
  set g : F → ℂ := fun ξ => f0 c (τ • algebraMap F (Ad F) ξ) with hg
  have hs : Summable g := (summable_norm_smul_algebraMap τ (unitaryTransvection_zero_second_mem_closure hH)).of_norm
  have h0 : g 0 = 0 := by simp only [hg, map_zero, smul_zero]; exact test_function_at_zero c
  rw [adelicTheta]
  change _ = ∑' ξ : F, g ξ
  rw [hs.tsum_eq_add_tsum_ite 0, h0, zero_add]
  have e1 : zeroRow c τ = ∑' x : {ξ : F // ξ ≠ 0}, g x := by
    rw [← (unitsEquivNeZero (G₀ := F)).tsum_eq]
    refine tsum_congr fun b => ?_
    simp only [g, f0, Units.smul_def]
    rfl
  rw [e1, show (∑' x : {ξ : F // ξ ≠ 0}, g x) = ∑' x : ({ξ : F | ξ ≠ 0} : Set F), g x from rfl,
    tsum_subtype {ξ : F | ξ ≠ 0} g]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ = 0
  · simp [h]
  · simp [h]

theorem bound_large {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    ∃ M : ℝ, ∀ t : {r : ℝ // 0 < r}, 1 ≤ (t : ℝ) → ∀ u ∈ normOneFundamentalDomain F,
      ‖zeroRow c (tau t u)‖ ≤ ((t : ℝ) ^ 2)⁻¹ * M := by
  have hC : IsCompact ((Subtype.val : normOneSubgroup F → IdeleGroup F) '' closure (normOneFundamentalDomain F)) :=
    (isCompact_closure_normOneFundamentalDomain F).image continuous_subtype_val
  obtain ⟨M, hM⟩ := exists_norm_adelicTheta_sub_le (w0 F) (unitaryTransvection_zero_second_mem_closure hH) hC 2
  refine ⟨M, fun t ht u hu => ?_⟩
  have := hM (u : IdeleGroup F) ⟨u, subset_closure hu, rfl⟩ t ht
  rwa [test_function_at_zero, sub_zero, ← zeroRow_eq c hH] at this

theorem bound_small {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    ∃ M : ℝ, ∀ t : {r : ℝ // 0 < r}, (t : ℝ) ≤ 1 → ∀ u ∈ normOneFundamentalDomain F,
      ‖zeroRow c (tau t u)‖ ≤ (t : ℝ) * M := by
  have hC : IsCompact ((fun x : IdeleGroup F => x⁻¹) ''
      ((Subtype.val : normOneSubgroup F → IdeleGroup F) '' closure (normOneFundamentalDomain F))) :=
    ((isCompact_closure_normOneFundamentalDomain F).image continuous_subtype_val).image continuous_inv
  obtain ⟨M, hM⟩ := exists_norm_adelicTheta_sub_le (w0 F) (adelicFourier_mem_schwartzBruhat (unitaryTransvection_zero_second_mem_closure hH)) hC 2
  refine ⟨M, fun t ht u hu => ?_⟩
  have ht0 : 0 < (t : ℝ) := t.2
  have hti : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
    rw [Positive.coe_inv]; exact (one_le_inv₀ ht0).2 ht
  have h1 := hM ((u : IdeleGroup F)⁻¹) ⟨u, ⟨u, subset_closure hu, rfl⟩, rfl⟩ t⁻¹ hti
  rw [fourier_test_function_at_zero hH, sub_zero] at h1
  have hinv : (tau t u)⁻¹ = moduleSection (w0 F) t⁻¹ * (u : IdeleGroup F)⁻¹ := by
    rw [tau, mul_inv, map_inv, mul_comm]
  have hmod : (ideleModule F (tau t u) : ℝ) = t := by
    have hu1 : ideleModule F (u : IdeleGroup F) = 1 := u.2
    rw [tau, map_mul, ideleModule_moduleSection, hu1, mul_one]
  rw [zeroRow_eq c hH, adelicTheta_eq (unitaryTransvection_zero_second_mem_closure hH), hinv, hmod, norm_mul]
  rw [Positive.coe_inv] at h1
  have h2 : ‖(((t : ℝ) : ℂ))⁻¹‖ = (t : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  rw [h2]
  calc (t : ℝ)⁻¹ * ‖adelicTheta (adelicFourier F (f0 c)) (moduleSection (w0 F) t⁻¹ * (u : IdeleGroup F)⁻¹)‖
      ≤ (t : ℝ)⁻¹ * ((((t : ℝ))⁻¹ ^ 2)⁻¹ * M) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht0.le)
    _ = (t : ℝ) * M := by field_simp

theorem lintegral_min_lt_top :
    ∫⁻ t, ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure < ⊤ := by
  have hmeas : Measurable fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_subtype_val.min (continuous_subtype_val.inv₀ fun t => t.2.ne')).measurable)
  rw [posRealMeasure_eq_map_expPos, lintegral_map hmeas measurable_expPos]
  have key : ∀ y : ℝ, 0 ≤ y → (Real.exp y)⁻¹ ≤ 2 * (1 + y ^ 2)⁻¹ := fun y hy => by
    have h1 := Real.quadratic_le_exp_of_nonneg hy
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (Real.exp_pos y)]
    nlinarith
  have hle : ∀ x : ℝ, ENNReal.ofReal (min ((expPos x : {r : ℝ // 0 < r}) : ℝ)
      ((expPos x : {r : ℝ // 0 < r}) : ℝ)⁻¹) ≤ ENNReal.ofReal (2 * (1 + x ^ 2)⁻¹) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    simp only [coe_expPos]
    rcases le_total 0 x with hx | hx
    · exact (min_le_right _ _).trans (key x hx)
    · refine (min_le_left _ _).trans ?_
      have := key (-x) (by linarith)
      rwa [Real.exp_neg, inv_inv, neg_sq] at this
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (2 * (1 + x ^ 2)⁻¹) := lintegral_mono hle
    _ < ⊤ := (integrable_inv_one_add_sq.const_mul 2).lintegral_lt_top

theorem integrable_min : Integrable (fun t : {r : ℝ // 0 < r} => min (t : ℝ) (t : ℝ)⁻¹) posRealMeasure := by
  have hc : Continuous fun t : {r : ℝ // 0 < r} => min (t : ℝ) (t : ℝ)⁻¹ :=
    continuous_subtype_val.min (continuous_subtype_val.inv₀ fun t => t.2.ne')
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t =>
    le_min t.2.le (inv_nonneg.2 t.2.le))]
  exact lintegral_min_lt_top

theorem continuous_integrand {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    Continuous (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => zeroRow c (tau p.1 p.2) * wt ω p.1 p.2) := by
  have htau : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 :=
    ((continuous_moduleSection (w0 F)).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have h1 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => zeroRow c (tau p.1 p.2) := by
    simp only [zeroRow_eq c hH]
    exact (continuous_adelicTheta (unitaryTransvection_zero_second_mem_closure hH)).comp htau
  have h2 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ((ω.1 (tau p.1 p.2) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (ω.2.1.comp htau)
  have h3 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => wt ω p.1 p.2 :=
    (h2.inv₀ fun p => Units.ne_zero _).mul (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst))
  exact h1.mul h3

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L2

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L2 in
theorem zero_term_holds : SZero := by
  intro F _ _ _ ω c hH
  obtain ⟨M₁, h₁⟩ := bound_large hH
  obtain ⟨M₂, h₂⟩ := bound_small hH
  set C : ℝ := max (max M₁ M₂) 0
  have hE : MeasurableSet (normOneFundamentalDomain F) := measurableSet_normOneFundamentalDomain F
  have : IsFiniteMeasure ((normOneMeasure F).restrict (normOneFundamentalDomain F)) :=
    isFiniteMeasure_restrict.2 (normOneMeasure_normOneFundamentalDomain_lt_top F).ne
  have hg : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => (C * min (p.1 : ℝ) (p.1 : ℝ)⁻¹) * 1) (muE F) :=
    (integrable_min.const_mul C).mul_prod (integrable_const (1 : ℝ))
  refine hg.mono' (continuous_integrand hH).aestronglyMeasurable ?_
  have hae : ∀ᵐ p ∂(muE F), p.2 ∈ normOneFundamentalDomain F :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hE)
  filter_upwards [hae] with p hp
  obtain ⟨t, u⟩ := p
  have ht0 : 0 < (t : ℝ) := t.2
  have hw : ‖wt ω t u‖ = (t : ℝ) := by
    rw [wt, norm_mul, norm_inv, norm_omega_eq_one hH.fin, inv_one, one_mul, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
  rw [norm_mul, hw, mul_one]
  have hC1 : M₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : M₂ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  rcases le_total 1 (t : ℝ) with ht | ht
  · have hmin : min (t : ℝ) (t : ℝ)⁻¹ = (t : ℝ)⁻¹ := min_eq_right ((inv_le_one₀ ht0).2 ht |>.trans ht)
    rw [hmin]
    calc ‖zeroRow c (tau t u)‖ * (t : ℝ) ≤ ((t : ℝ) ^ 2)⁻¹ * M₁ * (t : ℝ) :=
          mul_le_mul_of_nonneg_right (h₁ t ht u hp) ht0.le
      _ ≤ ((t : ℝ) ^ 2)⁻¹ * C * (t : ℝ) := by gcongr
      _ = C * (t : ℝ)⁻¹ := by field_simp
  · have hmin : min (t : ℝ) (t : ℝ)⁻¹ = (t : ℝ) := min_eq_left (ht.trans ((one_le_inv₀ ht0).2 ht))
    rw [hmin]
    calc ‖zeroRow c (tau t u)‖ * (t : ℝ) ≤ (t : ℝ) * M₂ * (t : ℝ) :=
          mul_le_mul_of_nonneg_right (h₂ t ht u hp) ht0.le
      _ ≤ (t : ℝ) * C * 1 := by
          have : (t : ℝ) * M₂ ≤ (t : ℝ) * C := mul_le_mul_of_nonneg_left hC2 ht0.le
          exact mul_le_mul this ht ht0.le (mul_nonneg ht0.le hC0)
      _ = C * (t : ℝ) := by ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
