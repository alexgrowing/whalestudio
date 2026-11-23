import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.FinA

theorem cosetSum {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) [m.IsMulLeftInvariant] (U : Subgroup G) (hU : IsOpen (U : Set G)) (hm : m U ≠ ⊤) {C : Set G} (hC : IsCompact C) :
    ∃ (s : Finset G) (c : ℝ), ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : G → V),
      (∀ h, ∀ k ∈ U, F (h * k) = F h) → (∀ h, h ∉ C → F h = 0) → ∫ h, F h ∂m = ∑ h ∈ s, c • F h := by
  classical
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hfin : ((QuotientGroup.mk : G → G ⧸ U) '' C).Finite := (hC.image QuotientGroup.continuous_mk).finite_of_discrete
  refine ⟨hfin.toFinset.image Quotient.out, m.real U, fun V _ _ _ F hF h0 => ?_⟩
  rw [Finset.sum_image fun a _ b _ h => Quotient.out_injective h]
  have hpre : ∀ q : G ⧸ U, {h : G | (h : G ⧸ U) = q} = (fun h => (q.out)⁻¹ * h) ⁻¹' (U : Set G) := by
    intro q
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  have hmeas : ∀ q : G ⧸ U, MeasurableSet {h : G | (h : G ⧸ U) = q} := fun q => by
    rw [hpre]; exact hU.measurableSet.preimage (measurable_const_mul _)
  have hval : ∀ q : G ⧸ U, m {h : G | (h : G ⧸ U) = q} = m U := fun q => by
    rw [hpre, measure_preimage_mul]
  have hout : ∀ h : G, F ((h : G ⧸ U).out) = F h := fun h => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul U h
    rw [hk, hF _ _ k.2]
  have hF' : F = fun h => ∑ q ∈ hfin.toFinset, {h : G | (h : G ⧸ U) = q}.indicator (fun _ => F q.out) h := by
    funext h
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq, Set.Finite.mem_toFinset]
    split_ifs with hh
    · exact (hout h).symm
    · exact h0 h fun hc => hh ⟨h, hc, rfl⟩
  conv_lhs => rw [hF']
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), Measure.real, hval, Measure.real]
  · intro q _
    exact (integrableOn_const (by rw [hval]; exact hm)).integrable_indicator (hmeas q)

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

section Reps

variable {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

theorem reps_ext {v w : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w φ) : v = w := by
  refine Lp.ext ?_
  have hm := map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)
  refine Measure.ae_le_iff_absolutelyContinuous.2 (hm ▸ Measure.AbsolutelyContinuous.rfl :
    quotientMeasure (Gam K n) μ ≪ Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))) ?_
  refine (ae_map_iff (measurable_mk _).aemeasurable
    ((Lp.stronglyMeasurable v).measurableSet_eq_fun (Lp.stronglyMeasurable w))).2 (ae_restrict_of_ae ?_)
  filter_upwards [hv, hw] with y h1 h2
  rw [h1, h2]

theorem reps_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) {v : ι → L2 μ} {φ : ι → G1 K n → ℂ} (h : ∀ i ∈ s, Reps μ (v i) (φ i)) :
    Reps μ (∑ i ∈ s, c i • v i) fun y => ∑ i ∈ s, c i * φ i y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa using hy
  | insert a s ha ih =>
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c a • v a) (∑ i ∈ s, c i • v i)),
      (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c a) (v a)), h a (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)] with y h1 h2 h3 h4
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, smul_eq_mul]

theorem reps_right {v : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) fun y => φ (y * g) := by
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v),
    (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hv] with y h1 h2
  rw [h1, rightMul_mk, h2]

end Reps

local notation "pf" => MultiplicityOne.finProj K n

theorem coe_pf {k : AdelicGLn.FiniteAdelicGL K n} (hk : k ∈ AdelicGLn.integralFiniteGL K n) :
    ((pf k : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n k := by
  rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hk))]

theorem pf_mem {k : AdelicGLn.FiniteAdelicGL K n} (hk : k ∈ AdelicGLn.integralFiniteGL K n) : pf k ∈ KG K n := by
  show ((pf k : G1 K n) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
  rw [coe_pf hk]; exact finEmb_mem_maxCompact hk

theorem split_KG {u : G1 K n} (hu : u ∈ KG K n) : ∃ a ∈ KG K n, ∃ k ∈ AdelicGLn.integralFiniteGL K n, u = a * pf k ∧
    (AdelicGLn.prodEquiv K n a).2 = 1 ∧ ∀ h, a * pf h = pf h * a := by
  have hu' : (u : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact := hu
  have ha := infEmb_archPart_mem_maxCompact hu'
  refine ⟨⟨_, maxCompact_le_normOneGL ha⟩, ha, _, finPart_mem_integralFiniteGL hu', Subtype.ext ?_, ?_, fun h => Subtype.ext ?_⟩
  · rw [Subgroup.coe_mul, coe_pf (finPart_mem_integralFiniteGL hu')]
    exact (infEmb_archPart_mul_finEmb_finPart _).symm
  · simp only [prodEquiv_infEmb]
  · simp only [Subgroup.coe_mul, MultiplicityOne.coe_finProj]
    rw [← mul_assoc, infEmb_mul_finEmb_comm, mul_assoc, mul_assoc, centralSection_inv_mul_comm]

variable {D : TypeDat K n} {Kf : Subgroup (AdelicGLn.FiniteAdelicGL K n)}

theorem pf_mem_iff (hL : D.Level Kf) {k : AdelicGLn.FiniteAdelicGL K n} (hk : k ∈ AdelicGLn.integralFiniteGL K n) :
    pf k ∈ D.U ↔ k ∈ Kf := by
  rw [hL.1 (pf k) (by rw [coe_pf hk, prodEquiv_finEmb]), coe_pf hk, prodEquiv_finEmb]

theorem lev_open (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K n) : IsOpen (Kf : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  obtain ⟨O, hO, h⟩ := D.isOpen
  have : (Kf : Set (AdelicGLn.FiniteAdelicGL K n)) = finEmb K n ⁻¹' O ∩ AdelicGLn.integralFiniteGL K n := by
    ext k
    constructor
    · intro hk
      have := ((h _).1 ((pf_mem_iff hL (hle hk)).2 hk)).1
      rw [coe_pf (hle hk)] at this
      exact ⟨this, hle hk⟩
    · rintro ⟨h1, h2⟩
      refine (pf_mem_iff hL h2).1 ((h _).2 ⟨?_, pf_mem h2⟩)
      rw [coe_pf h2]; exact h1
  rw [this]
  exact (hO.preimage continuous_finEmb).inter (AdelicGLn.isOpen_integralFiniteGL K n)

theorem split_U (hL : D.Level Kf) {u : G1 K n} (hu : u ∈ D.U) : ∃ a ∈ KG K n, ∃ k ∈ Kf, u = a * pf k ∧ ∀ h, a * pf h = pf h * a := by
  obtain ⟨a, ha, k, hk, e, h1, h2⟩ := split_KG ((typeFin D).2.1 hu)
  refine ⟨a, ha, k, (pf_mem_iff hL hk).1 ?_, e, h2⟩
  have : pf k = a⁻¹ * u := by rw [e, inv_mul_cancel_left]
  rw [this]
  exact D.U.mul_mem (D.U.inv_mem (hL.2.1 a h1 ha)) hu

theorem fix_inv (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K n) {f : G1 K n → ℂ} (hf : D.Fix f) (g : G1 K n)
    {k : AdelicGLn.FiniteAdelicGL K n} (hk : k ∈ Kf) : f (g * pf k) = f g := by
  have hU := (pf_mem_iff hL (hle hk)).2 hk
  rw [← hf g, ← hf (g * pf k), ← (D.inv _ hU).integral_comp (MeasurableEquiv.mulLeft (pf k)).measurableEmbedding
    fun u => D.e u * f (g * u)]
  refine integral_congr_ae ?_
  filter_upwards [D.supp] with u hu
  rw [hL.2.2 _ hU (by rw [coe_pf (hle hk), prodEquiv_finEmb]) u hu, mul_assoc]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.FinA

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.FinA

variable {K : Type} [Field K] [NumberField K]

local notation "pf" => MultiplicityOne.finProj K (2 + 2)
local notation "GF" => AdelicGLn.FiniteAdelicGL K (2 + 2)

noncomputable def dl (x : G1 K (2 + 2)) (h : GF) : ℝ := HH (x * pf h) - HH x

theorem dl_left (X : UPos (2 + 2) 2 → AdeleRing (𝓞 K) K) (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)) (h : GF) :
    dl (nn X * lv m₁ m₂ t * g) h = dl g h := by
  rw [dl, dl, mul_assoc _ g, hpSpec.1, hpSpec.1]; ring

theorem dl_nn (X : UPos (2 + 2) 2 → AdeleRing (𝓞 K) K) (g : G1 K (2 + 2)) (h : GF) : dl (nn X * g) h = dl g h := by
  rw [← dl_left X 1 1 0 g h, blkLaws.2.2.1, mul_one]

theorem dl_lv (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)) (h : GF) : dl (lv m₁ m₂ t * g) h = dl g h := by
  rw [← dl_nn 0, ← mul_assoc, dl_left]

theorem dl_right (x : G1 K (2 + 2)) (h : GF) {k : GF} (hk : k ∈ AdelicGLn.integralFiniteGL K (2 + 2)) : dl x (h * k) = dl x h := by
  rw [dl, dl, map_mul, ← mul_assoc, (hpSpec.2.1 _ (pf_mem hk)).2]

theorem dl_comm (x : G1 K (2 + 2)) (h : GF) {a : G1 K (2 + 2)} (ha : a ∈ KG K (2 + 2)) (hc : ∀ h, a * pf h = pf h * a) {k : GF}
    (hk : k ∈ AdelicGLn.integralFiniteGL K (2 + 2)) : dl (x * (a * pf k)) h = dl x (k * h) := by
  rw [dl, dl, (hpSpec.2.1 _ ((KG K (2 + 2)).mul_mem ha (pf_mem hk))).2, mul_assoc x, mul_assoc a, ← map_mul, hc, ← mul_assoc,
    (hpSpec.2.1 _ ha).2]

theorem dl_fin (h : GF) : (Set.range fun x : G1 K (2 + 2) => dl x h).Finite := by
  have hlc : IsLocallyConstant fun y : GF => dl (1 : G1 K (2 + 2)) y := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have ho : IsOpen ((fun z : GF => y⁻¹ * z) ⁻¹' AdelicGLn.integralFiniteGL K (2 + 2)) :=
      (AdelicGLn.isOpen_integralFiniteGL K (2 + 2)).preimage (continuous_const.mul continuous_id)
    filter_upwards [ho.mem_nhds (show y⁻¹ * y ∈ AdelicGLn.integralFiniteGL K (2 + 2) by rw [inv_mul_cancel]; exact one_mem _)] with z hz
    rw [← dl_right 1 y hz, mul_inv_cancel_left]
  haveI : CompactSpace (AdelicGLn.integralFiniteGL K (2 + 2)) := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K _)
  have h2 := (hlc.comp_continuous (f := fun k : AdelicGLn.integralFiniteGL K (2 + 2) => (k : GF) * h)
    (continuous_subtype_val.mul continuous_const)).range_finite
  refine h2.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨X, m₁, m₂, t, u, hu, rfl⟩ := iwa x
  obtain ⟨a, ha, k, hk, rfl, -, hc⟩ := split_KG hu
  refine ⟨⟨k, hk⟩, ?_⟩
  simp only [Function.comp]
  rw [dl_left, ← dl_comm 1 h ha hc hk, one_mul]

theorem dl_cont (ω : ℝ → ℂ) (h : GF) : Continuous (fun x : G1 K (2 + 2) => ω (dl x h)) ∧ ∃ C : ℝ, ∀ x : G1 K (2 + 2), ‖ω (dl x h)‖ ≤ C := by
  have hc : Continuous fun x : G1 K (2 + 2) => dl x h :=
    (hpSpec.2.2.2.1.comp (continuous_id.mul continuous_const)).sub hpSpec.2.2.2.1
  haveI := (dl_fin h).to_subtype
  refine ⟨?_, ?_⟩
  · exact (continuous_of_discreteTopology (f := fun r : Set.range fun x : G1 K (2 + 2) => dl x h => ω r)).comp
      (hc.subtype_mk fun x => ⟨x, rfl⟩)
  · obtain ⟨C, hC⟩ := ((dl_fin h).image fun r => ‖ω r‖).bddAbove
    exact ⟨C, fun x => hC ⟨_, ⟨x, rfl⟩, rfl⟩⟩

def Rule (m : Measure GF) (e : TF K (2 + 2)) (Kf : Subgroup GF) (s : Finset GF) (c : GF → ℂ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (F : GF → V),
    (∀ h, ∀ k ∈ Kf, F (h * k) = F h) → ∫ h, e h • F h ∂m = ∑ h ∈ s, c h • F h

theorem rule_ex {D : TypeDat K (2 + 2)} {Kf : Subgroup GF} (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K (2 + 2))
    (m : Measure GF) [m.IsHaarMeasure] (e : TF K (2 + 2)) (he : ∀ k ∈ Kf, ∀ h, e (h * k) = e h) : ∃ s c, Rule m e Kf s c := by
  obtain ⟨s, c, h⟩ := cosetSum m Kf (lev_open hL hle)
    (ne_top_of_le_ne_top (AdelicGLn.isCompact_integralFiniteGL K (2 + 2)).measure_lt_top.ne (measure_mono hle)) e.hasCompactSupport
  refine ⟨s, fun h => c * e h, fun V _ _ _ F hF => ?_⟩
  rw [h V (fun h => e h • F h) (fun h k hk => by rw [he k hk, hF h k hk])
    fun h hh => by rw [image_eq_zero_of_notMem_tsupport hh, zero_smul]]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_smul, Complex.coe_smul]

noncomputable def lin (s : Finset GF) (c : GF → ℂ) (ω : ℝ → ℂ) : (G1 K (2 + 2) → ℂ) →ₗ[ℂ] (G1 K (2 + 2) → ℂ) where
  toFun f x := ∑ h ∈ s, c h * ω (dl x h) * f (x * pf h)
  map_add' f f' := by funext x; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring

theorem lin_apply (s : Finset GF) (c : GF → ℂ) (ω : ℝ → ℂ) (f : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) :
    lin s c ω f x = ∑ h ∈ s, c h * ω (dl x h) * f (x * pf h) := rfl

theorem lin_fix {D : TypeDat K (2 + 2)} {Kf : Subgroup GF} (hL : D.Level Kf) (hle : Kf ≤ AdelicGLn.integralFiniteGL K (2 + 2))
    {m : Measure GF} [m.IsHaarMeasure] {e : TF K (2 + 2)} (he : ∀ k ∈ Kf, ∀ h, e (k * h) = e h) {s : Finset GF} {c : GF → ℂ}
    (hr : Rule m e Kf s c) (ω : ℝ → ℂ) {f : G1 K (2 + 2) → ℂ} (hc : Continuous f) (hf : D.Fix f) : D.Fix (lin s c ω f) := by
  intro g
  have key : ∀ u ∈ D.U, lin s c ω f (g * u) = ∑ h ∈ s, c h * ω (dl g h) * f (g * pf h * u) := by
    intro u hu
    obtain ⟨a, ha, k, hk, rfl, hcm⟩ := split_U hL hu
    have h1 := hr ℂ (fun h => ω (dl (g * (a * pf k)) h) * f (g * (a * pf k) * pf h)) fun h k' hk' => by
      rw [dl_right _ _ (hle hk'), map_mul, ← mul_assoc _ (pf h), fix_inv hL hle hf _ hk']
    have h2 := hr ℂ (fun h => ω (dl g h) * f (g * pf h * a)) fun h k' hk' => by
      rw [dl_right _ _ (hle hk'), map_mul, ← mul_assoc, mul_assoc _ _ a, ← hcm, ← mul_assoc, fix_inv hL hle hf _ hk']
    rw [← integral_mul_left_eq_self _ k] at h2
    simp only [lin_apply, smul_eq_mul, mul_assoc (c _)] at h1 h2 ⊢
    rw [← h1]
    simp only [← mul_assoc (g * _) a, fix_inv hL hle hf _ hk]
    rw [← h2]
    congr 1
    funext h
    rw [he k hk, dl_comm g h ha hcm (hle hk), mul_assoc g (a * _), mul_assoc a, ← map_mul, hcm, ← mul_assoc g]
  haveI := D.prob
  haveI : IsFiniteMeasureOnCompacts D.ν := ⟨fun _ _ => measure_lt_top _ _⟩
  have hint : ∀ y : G1 K (2 + 2), Integrable (fun u => D.e u * f (y * u)) D.ν := fun y => by
    have := (D.cont.mul (hc.comp (continuous_const.mul continuous_id : Continuous fun u => y * u))).continuousOn.integrableOn_compact
      (μ := D.ν) (typeFin D).1
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem D.supp] at this
  rw [integral_congr_ae (g := fun u => ∑ h ∈ s, c h * ω (dl g h) * (D.e u * f (g * pf h * u))), integral_finset_sum, lin_apply]
  · exact Finset.sum_congr rfl fun h _ => by rw [integral_const_mul, hf]
  · exact fun h _ => (hint _).const_mul _
  · filter_upwards [D.supp] with u hu
    rw [key u hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring

theorem lin_sec [IsTotallyComplex K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)}
    (h₁ : CuspIrr μ₂ τ₁) (h₂ : CuspIrr μ₂ τ₂) (s : Finset GF) (c : GF → ℂ) (ω : ℝ → ℂ) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f)
    (hf : D.Fix f) (hf' : D.Fix (lin s c ω f)) : IsSec τ₁ τ₂ (lin s c ω f) := by
  obtain ⟨hc, ⟨C, hC⟩, hn, hray, hsl⟩ := (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hf).1 hs
  refine (secCrit μ₂ τ₁ τ₂ D h₁ h₂ _ hf').2 ⟨?_, ?_, fun X g => ?_, fun t g => ?_, fun g => ⟨fun m₂ => ?_, fun m₁ => ?_⟩⟩
  · exact continuous_finset_sum s fun h _ =>
      (continuous_const.mul (dl_cont ω h).1).mul (hc.comp (continuous_id.mul continuous_const))
  · choose B hB using fun h : GF => (dl_cont ω h).2
    refine ⟨∑ h ∈ s, ‖c h‖ * B h * C, fun g => (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB h g) (norm_nonneg _)) (hC _) (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hB h g)))
  · simp only [lin_apply, dl_nn, mul_assoc (nn X), hn]
  · simp only [lin_apply, dl_lv, mul_assoc (lv 1 1 t), hray]
  · choose v hv hv' using fun h : GF => (hsl (g * pf h)).1 m₂
    refine ⟨∑ h ∈ s, (c h * ω (dl g h)) • v h, τ₁.sum_mem fun h _ => τ₁.smul_mem _ (hv h), ?_⟩
    simpa only [lin_apply, dl_lv, mul_assoc (lv _ _ _)] using reps_sum s (fun h => c h * ω (dl g h)) fun h _ => hv' h
  · choose v hv hv' using fun h : GF => (hsl (g * pf h)).2 m₁
    refine ⟨∑ h ∈ s, (c h * ω (dl g h)) • v h, τ₂.sum_mem fun h _ => τ₂.smul_mem _ (hv h), ?_⟩
    simpa only [lin_apply, dl_lv, mul_assoc (lv _ _ _)] using reps_sum s (fun h => c h * ω (dl g h)) fun h _ => hv' h

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.FinA
