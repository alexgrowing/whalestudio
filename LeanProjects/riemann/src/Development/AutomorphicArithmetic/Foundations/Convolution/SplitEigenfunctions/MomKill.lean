import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomChar
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CharZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ProdExt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GaussSchwartz

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

private theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

private theorem td_fin (F : Type) [Field F] [NumberField F] :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) :=
    fun v => td_adic v
  refine ⟨isTotallyDisconnected_of_image (f := fun (x : FiniteAdeleRing (𝓞 F) F) v => x v)
    (continuous_pi fun v => RestrictedProduct.continuous_eval v).continuousOn
    (fun x y h => Subtype.ext (funext fun v => congrFun h v))
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem basis_fin (F : Type) [Field F] [NumberField F] :
    TopologicalSpace.IsTopologicalBasis
      {T : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F) | IsCompact T ∧ IsOpen T} := by
  haveI := td_fin F
  have hb : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun T hT => hT.2) ?_
  intro x U hx hU
  obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCU⟩ := hb.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨C, ⟨hKc.of_isClosed_subset hC.isClosed (hCU.trans interior_subset), hC.isOpen⟩, hxC,
    hCU.trans (interior_subset.trans hKU)⟩

private theorem exhaust (F : Type) [Field F] [NumberField F] :
    ∃ e : ℕ → Set (Fin 4 → FiniteAdeleRing (𝓞 F) F),
      (∀ n, IsCompact (e n) ∧ IsOpen (e n)) ∧ Monotone e ∧ ∀ x, ∃ n, x ∈ e n := by
  have hB := basis_fin F
  obtain ⟨T, hTc, hTs, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
    {T : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F) | IsCompact T ∧ IsOpen T} (fun t ht => ht.2)
  have hne : (insert ∅ T).Nonempty := Set.insert_nonempty _ _
  obtain ⟨e, he⟩ := (hTc.insert ∅).exists_eq_range hne
  have h1 : ∀ n, IsCompact (e n) ∧ IsOpen (e n) := by
    intro n
    have hn : e n ∈ insert ∅ T := he ▸ Set.mem_range_self n
    rcases hn with hn | hn
    · rw [hn]; exact ⟨isCompact_empty, isOpen_empty⟩
    · exact hTs hn
  have hU : ⋃ n, e n = Set.univ := by
    rw [← Set.sUnion_range, ← he, Set.sUnion_insert, Set.empty_union, hTU, hB.sUnion_eq]
  refine ⟨Set.accumulate e, fun n => ⟨isCompact_accumulate (fun i => (h1 i).1) n, ?_⟩,
    Set.monotone_accumulate, fun x => ?_⟩
  · rw [Set.accumulate_def]
    exact isOpen_biUnion (fun i _ => (h1 i).2)
  · have hmem : x ∈ ⋃ n, e n := hU ▸ Set.mem_univ _
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
    exact ⟨n, Set.mem_accumulate.2 ⟨n, le_rfl, hn⟩⟩

section
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

private theorem cont_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cont_pInf : Continuous (TR.pInf F) := (cont_symm F).comp continuous_fst

private noncomputable def xc (v : V4 F) : Fin 4 × InfinitePlace F → ℝ := fun p => TR.pInf F (v p.1) p.2

private noncomputable def ec (y : (Fin 4 × InfinitePlace F → ℝ) × (Fin 4 → FiniteAdeleRing (𝓞 F) F)) :
    V4 F :=
  fun i => ((TR.infEq F (fun w => y.1 (i, w)), y.2 i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

private theorem cont_xc : Continuous (xc F) :=
  continuous_pi fun p => (continuous_apply p.2).comp ((cont_pInf F).comp (continuous_apply p.1))

private theorem cont_fin : Continuous (finPartPi : V4 F → Fin 4 → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

private theorem cont_ec : Continuous (ec F) := by
  refine continuous_pi fun i => ?_
  exact ((TR.continuous_infEq F).comp (continuous_pi fun w =>
    (continuous_apply (i, w)).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

private theorem ec_xc (v : V4 F) : ec F (xc F v, finPartPi v) = v := by
  funext i
  refine TR.ad_ext ?_ rfl
  exact (TR.infEq F).symm_apply_apply _

private theorem poly_mem (t : Fin 4 × InfinitePlace F → ℝ) (n : ℕ) :
    (fun v : V4 F => ((∑ p, t p * xc F v p : ℝ) : ℂ) ^ n) ∈ polyFn (F := F) := by
  have h : (fun v : V4 F => ((∑ p, t p * xc F v p : ℝ) : ℂ))
      = ∑ p, (t p : ℂ) • (fun v : V4 F => ((TR.pInf F (v p.1) p.2 : ℝ) : ℂ)) := by
    funext v
    simp [Finset.sum_apply, xc]
  have h1 : (fun v : V4 F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) ∈ polyFn (F := F) := by
    rw [h]
    refine Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (show _ ∈ {g : V4 F → ℂ | ∃ i w, g = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)} from ⟨p.1, p.2, rfl⟩)
  exact Subalgebra.pow_mem _ h1 n

private theorem mom4 (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : Ω → V4 F) (ρ : Ω → ℂ)
    (hr : Measurable r)
    (hint : ∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * ∑ p, |xc F (r ω) p|) : ℝ) : ℂ) * ρ ω) ν)
    (hmom : ∀ P ∈ polyFn (F := F), ∀ T : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
      ∫ ω, P (r ω) * T.indicator 1 (finPartPi (r ω)) * ρ ω ∂ν = 0)
    (q : V4 F → ℂ) (hq : Measurable q) (hq1 : ∀ x, ‖q x‖ ≤ 1) : ∫ ω, q (r ω) * ρ ω ∂ν = 0 := by
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hX : Measurable fun ω => xc F (r ω) := (cont_xc F).measurable.comp hr
  have hs : Measurable fun ω => (finPartPi (r ω) : Fin 4 → FiniteAdeleRing (𝓞 F) F) :=
    (cont_fin F).measurable.comp hr
  have hT : ∀ (T : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (S : Set (Fin 4 × InfinitePlace F → ℝ)),
      MeasurableSet S → IsCompact T → IsOpen T →
      ∫ ω, S.indicator 1 (xc F (r ω)) * (T.indicator 1 (finPartPi (r ω)) * ρ ω) ∂ν = 0 := by
    intro T S hS hTc hTo
    have hi : Measurable fun ω => T.indicator (1 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) :=
      (measurable_one.indicator hTo.measurableSet).comp hs
    have hib : ∀ ω, ‖T.indicator (1 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))‖ ≤ 1 := by
      intro ω
      by_cases h : finPartPi (r ω) ∈ T <;> simp [h]
    have hI : ∀ g : Ω → ℂ, Integrable g ν →
        Integrable (fun ω => T.indicator (1 : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) * g ω) ν :=
      fun g hg => hg.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)
    refine charZero Ω _ ν _ _ hX (hI ρ hρ) ?_ S hS
    refine momChar Ω _ ν _ _ hX (fun R => ?_) (fun n t => ?_)
    · refine (hI _ (hint R)).congr (Eventually.of_forall fun ω => ?_)
      simp only
      ring
    · have := hmom _ (poly_mem F t n) T hTc hTo
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      ring
  have hQ : Measurable fun y => q (ec F y) := hq.comp (cont_ec F).measurable
  have := prodExt Ω _ _ ν (fun ω => xc F (r ω)) (fun ω => finPartPi (r ω)) ρ (basis_fin F) hX hs hρ
    (fun S T hS hTc hTo => hT T S hS hTc hTo) _ hQ (fun y => hq1 _)
  simpa only [ec_xc] using this

private theorem coord_inf (v : V4 F) (i : Fin 4) (w : InfinitePlace F) :
    (infPartPi v i).1 ⟨w, IsTotallyReal.isReal w⟩ = TR.pInf F (v i) w := by
  simp only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change _ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((v i).1 w)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

private theorem norm_inf_le (v : V4 F) : ‖infPartPi v‖ ≤ ∑ p, |xc F v p| := by
  have h0 : 0 ≤ ∑ p, |xc F v p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg h0).2 fun w => ?_) ((pi_norm_le_iff_of_nonneg h0).2 fun w => ?_)
  · have h1 : (infPartPi v i).1 w = xc F v (i, w.1) := coord_inf F v i w.1
    rw [h1, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun p => |xc F v p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, w.1))
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

private theorem cont_gauss (δ : F) : Continuous (gauss δ) := by
  unfold gauss
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_finset_sum _ fun w _ => (continuous_apply w).comp ((cont_pInf F).comp ?_))))
  fun_prop

private theorem gauss_ne (δ : F) (v : V4 F) : gauss δ v ≠ 0 := Complex.exp_ne_zero _

end

private theorem qInf_ge (δ : ℚ) (hδ : δ < 0) : ∃ c : ℝ, 0 < c ∧ ∀ v : V4 ℚ,
    c * ∑ p, xc ℚ v p ^ 2 ≤ qInf δ v := by
  have hd0 : (δ : ℝ) < 0 := by exact_mod_cast hδ
  refine ⟨min 1 (-(2 * (δ : ℝ))), lt_min one_pos (by linarith), fun v => ?_⟩
  rw [qInf, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have hd : TR.pInf ℚ (rt δ) w = (δ : ℝ) := by
    exact (congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap ℚ δ) w).trans
      (eq_ratCast (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)) δ)
  simp only [map_add, map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply,
    map_ofNat, Pi.ofNat_apply, hd, Fin.sum_univ_four, xc]
  have h1 : min 1 (-(2 * (δ : ℝ))) ≤ 1 := min_le_left _ _
  have h2 : min 1 (-(2 * (δ : ℝ))) ≤ -(2 * (δ : ℝ)) := min_le_right _ _
  have e0 := sq_nonneg (TR.pInf ℚ (v 0) w)
  have e1 := sq_nonneg (TR.pInf ℚ (v 1) w)
  have e2 := sq_nonneg (TR.pInf ℚ (v 2) w)
  have e3 := sq_nonneg (TR.pInf ℚ (v 3) w)
  nlinarith [mul_le_mul_of_nonneg_right h1 e0, mul_le_mul_of_nonneg_right h1 e1,
    mul_le_mul_of_nonneg_right h1 e2, mul_le_mul_of_nonneg_right h2 e3]

private theorem norm_gauss (δ : ℚ) (v : V4 ℚ) : ‖gauss δ v‖ = Real.exp (-Real.pi * qInf δ v) := by
  rw [gauss_eq, Complex.norm_exp]
  congr 1
  simp

private theorem exp_bound (δ : ℚ) (hδ : δ < 0) (R : ℝ) (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V4 ℚ,
    Real.exp (R * ∑ p, |xc ℚ v p|) * ‖gauss δ v‖ * (1 + ‖infPartPi v‖) ^ N ≤ C := by
  obtain ⟨c, hc, hq⟩ := qInf_ge δ hδ
  set b : ℝ := Real.pi * c with hb
  have hbp : 0 < b := mul_pos Real.pi_pos hc
  set D : ℝ := (R + 1) ^ 2 / (4 * b) with hD
  refine ⟨(N.factorial : ℝ) * Real.exp (1 + ∑ _p : Fin 4 × InfinitePlace ℚ, D), by positivity, fun v => ?_⟩
  set s : ℝ := ∑ p, |xc ℚ v p| with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : (1 + ‖infPartPi v‖) ^ N ≤ (N.factorial : ℝ) * Real.exp (1 + s) := by
    have h2 : (1 + ‖infPartPi v‖) ^ N ≤ (1 + s) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_inf_le ℚ v]) N
    have h3 := Real.pow_div_factorial_le_exp (1 + s) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by positivity
    rw [div_le_iff₀ hf] at h3
    linarith
  have h4 : (R + 1) * s - b * ∑ p, xc ℚ v p ^ 2 ≤ ∑ _p : Fin 4 × InfinitePlace ℚ, D := by
    rw [hs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    have e : D - ((R + 1) * |xc ℚ v p| - b * xc ℚ v p ^ 2) =
        (2 * b * |xc ℚ v p| - (R + 1)) ^ 2 / (4 * b) := by
      rw [hD]
      field_simp
      rw [← sq_abs (xc ℚ v p)]
      ring
    have : 0 ≤ D - ((R + 1) * |xc ℚ v p| - b * xc ℚ v p ^ 2) := by
      rw [e]; positivity
    linarith
  have h5 : b * ∑ p, xc ℚ v p ^ 2 ≤ Real.pi * qInf δ v := by
    rw [hb, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hq v) Real.pi_pos.le
  rw [norm_gauss]
  calc Real.exp (R * s) * Real.exp (-Real.pi * qInf δ v) * (1 + ‖infPartPi v‖) ^ N
      ≤ Real.exp (R * s) * Real.exp (-Real.pi * qInf δ v) * ((N.factorial : ℝ) * Real.exp (1 + s)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (N.factorial : ℝ) * Real.exp (R * s + -Real.pi * qInf δ v + (1 + s)) := by
        rw [Real.exp_add (R * s + -Real.pi * qInf δ v) (1 + s), Real.exp_add (R * s) (-Real.pi * qInf δ v)]
        ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith

private theorem fock_ind (δ : ℚ) (hδ : δ < 0) (P : V4 ℚ → ℂ) (hP : P ∈ polyFn (F := ℚ))
    (T : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (hTc : IsCompact T) (hTo : IsOpen T) :
    ∃ ph ∈ Fock δ, ∀ v, ph.1 v = P v * gauss δ v * T.indicator 1 (finPartPi v) := by
  have hδ' : ∀ e : ℚ →+* ℝ, e δ < 0 := fun e => by
    rw [eq_ratCast e δ]
    exact_mod_cast hδ
  have hg : T.indicator (1 : (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) ∈ finiteSchwartzBruhatPi ℚ (ι := Fin 4) := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
    · by_cases hx : x ∈ T
      · filter_upwards [hTo.mem_nhds hx] with y hy
        simp [Set.indicator, hx, hy]
      · filter_upwards [hTc.isClosed.isOpen_compl.mem_nhds hx] with y hy
        have hy' : y ∉ T := hy
        simp [Set.indicator, hx, hy']
    exact HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _
  have hm := pgMem ℚ δ hδ' Real.pi Real.pi_pos P hP _ hg
  refine ⟨⟨_, hm⟩, ?_, fun v => ?_⟩
  · refine mem_fock.2 (Submodule.subset_span ⟨P, hP, _, hg, ?_⟩)
    funext v
    rw [gauss_eq]
  · simp
    rw [gauss_eq]
    simp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.momKill :
    MomKill := by
  intro δ hδ Y _ m _ p w hp hw hK hF Ψ hΨ hint
  have hfin : Measurable fun y => (finPartPi (p y) : Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (cont_fin ℚ).measurable.comp hp
  have hind : ∀ T : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ), IsOpen T →
      Measurable fun y => T.indicator (1 : (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ) (finPartPi (p y)) :=
    fun T hT => (measurable_one.indicator hT.measurableSet).comp hfin
  have hgm : Measurable fun y => gauss δ (p y) := (cont_gauss ℚ δ).measurable.comp hp
  have key : ∀ T₀ : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact T₀ → IsOpen T₀ →
      ∀ q : V4 ℚ → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) →
      ∫ y, q (p y) * (T₀.indicator 1 (finPartPi (p y)) * gauss δ (p y) * w y) ∂m = 0 := by
    intro T₀ hc ho q hq hq1
    refine mom4 ℚ Y m p _ hp (fun R => ?_) (fun P hP T hTc hTo => ?_) q hq hq1
    · obtain ⟨n, hn⟩ := hK T₀ hc
      obtain ⟨C, hC0, hC⟩ := exp_bound δ hδ R n
      have hxm : Measurable fun y => ((Real.exp (R * ∑ i, |xc ℚ (p y) i|) : ℝ) : ℂ) := by
        have h1 : Measurable fun y => xc ℚ (p y) := (cont_xc ℚ).measurable.comp hp
        have h2 : ∀ i, Measurable fun y => xc ℚ (p y) i := fun i => (measurable_pi_apply i).comp h1
        fun_prop
      refine (hn.norm.const_mul C).mono'
        ((hxm.mul (((hind T₀ ho).mul hgm).mul hw)).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
      by_cases hy : finPartPi (p y) ∈ T₀
      · have h1 := hC (p y)
        have hpos : 0 < (1 + ‖infPartPi (p y)‖) ^ n := by positivity
        have h2 : Real.exp (R * ∑ i, |xc ℚ (p y) i|) * ‖gauss δ (p y)‖ ≤
            C * ((1 + ‖infPartPi (p y)‖) ^ n)⁻¹ := by
          rw [le_mul_inv_iff₀ hpos]
          exact h1
        simp only [norm_mul, Complex.norm_real, wt, hy, if_true, Set.indicator_of_mem, Pi.one_apply,
          norm_one, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [abs_of_pos (inv_pos.2 hpos), ← mul_assoc, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      · simp only [Set.indicator_of_notMem hy]
        simp only [zero_mul, mul_zero, norm_zero]
        positivity
    · obtain ⟨ph, hph, he⟩ := fock_ind δ hδ P hP (T ∩ T₀) (hTc.inter_right hc.isClosed) (hTo.inter ho)
      have h0 := hF ph hph
      rw [← h0]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [he]
      by_cases h1 : finPartPi (p y) ∈ T <;> by_cases h2 : finPartPi (p y) ∈ T₀ <;>
        simp [Set.indicator, h1, h2]
      ring
  obtain ⟨e, he, hmono, hU⟩ := exhaust ℚ
  have hΨm : Measurable fun v => Ψ v / gauss δ v := hΨ.div (cont_gauss ℚ δ).measurable
  let Aₙ : ℕ → Set (V4 ℚ) := fun n => {v | ‖Ψ v / gauss δ v‖ ≤ n}
  have hAm : ∀ n, MeasurableSet (Aₙ n) := fun n => measurableSet_le hΨm.norm measurable_const
  have hzero : ∀ n : ℕ, ∫ y, (Aₙ n).indicator 1 (p y) * (e n).indicator 1 (finPartPi (p y)) *
      (Ψ (p y) * w y) ∂m = 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h := key (e n) (he n).1 (he n).2
      (fun v => ((n : ℂ) + 1)⁻¹ * (Aₙ n).indicator (fun v => Ψ v / gauss δ v) v)
      (measurable_const.mul (hΨm.indicator (hAm n))) (fun v => by
        rw [norm_mul, norm_inv]
        have hnn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
          have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [hnn, inv_mul_le_iff₀ (by positivity), mul_one]
        by_cases hv : v ∈ Aₙ n
        · rw [Set.indicator_of_mem hv]
          have : ‖Ψ v / gauss δ v‖ ≤ n := hv
          linarith
        · rw [Set.indicator_of_notMem hv]
          simp
          positivity)
    have h2 : ∫ y, ((n : ℂ) + 1)⁻¹ * ((Aₙ n).indicator 1 (p y) * (e n).indicator 1 (finPartPi (p y)) *
        (Ψ (p y) * w y)) ∂m = 0 := by
      rw [← h]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      have hg := gauss_ne ℚ δ (p y)
      by_cases h1 : p y ∈ Aₙ n <;> by_cases h2 : finPartPi (p y) ∈ e n <;>
        simp [Set.indicator, h1, h2]
      field_simp
    rw [integral_const_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left (inv_ne_zero hn1)
  have hlim : Tendsto (fun n : ℕ => ∫ y, (Aₙ n).indicator 1 (p y) * (e n).indicator 1 (finPartPi (p y)) *
      (Ψ (p y) * w y) ∂m) atTop (𝓝 (∫ y, Ψ (p y) * w y ∂m)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖Ψ (p y) * w y‖) (fun n => ?_) hint.norm
      (fun n => ?_) ?_
    · have ha : Measurable fun y => (Aₙ n).indicator (1 : V4 ℚ → ℂ) (p y) :=
        (measurable_one.indicator (hAm n)).comp hp
      exact (ha.mul (hind _ (he n).2)).aestronglyMeasurable.mul hint.1
    · refine ae_of_all _ fun y => ?_
      by_cases h1 : p y ∈ Aₙ n <;> by_cases h2 : finPartPi (p y) ∈ e n <;>
        simp [Set.indicator, h1, h2]
      all_goals positivity
    · refine ae_of_all _ fun y => ?_
      obtain ⟨n₁, hn₁⟩ := hU (finPartPi (p y))
      obtain ⟨n₂, hn₂⟩ := exists_nat_ge ‖Ψ (p y) / gauss δ (p y)‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max n₁ n₂)] with n hn
      have h1 : p y ∈ Aₙ n := by
        have : (n₂ : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
        exact hn₂.trans this
      have h2 : finPartPi (p y) ∈ e n := hmono ((le_max_left _ _).trans hn) hn₁
      simp [Set.indicator, h1, h2]
  exact tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
