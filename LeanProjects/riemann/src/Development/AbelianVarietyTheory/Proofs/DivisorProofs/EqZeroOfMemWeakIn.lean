import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre

noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspQuot

section Test

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Set V} {α : V → ℂ}

def IsTest (U : Set V) (α : V → ℂ) : Prop := ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U

theorem IsTest.continuous_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Continuous fun x => α x * G x :=
  continuous_of_tsupport fun x hx => h.1.continuous.continuousAt.mul
    (hG.continuousAt (hU.mem_nhds (h.2.2 (tsupport_mul_subset_left hx))))

theorem IsTest.add {β : V → ℂ} (h : IsTest U α) (h' : IsTest U β) : IsTest U (α + β) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, (tsupport_add α β).trans (Set.union_subset h.2.2 h'.2.2)⟩

theorem IsTest.mul (h : IsTest U α) {β : V → ℂ} (hβ : ContDiff ℝ ∞ β) : IsTest U fun x => α x * β x :=
  ⟨h.1.mul hβ, h.2.1.mul_right, tsupport_mul_subset_left.trans h.2.2⟩

theorem IsTest.fderiv (h : IsTest U α) (v : V) : IsTest U fun x => fderiv ℝ α x v :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩

theorem isTest_zero : IsTest U (0 : V → ℂ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem isTest_sum {ι : Type} (s : Finset ι) {f : ι → V → ℂ} (h : ∀ i, IsTest U (f i)) : IsTest U (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsTest U) (fun _ _ => IsTest.add) isTest_zero fun i _ => h i

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]

theorem IsTest.integrable_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Integrable (fun x => α x * G x) ν :=
  (h.continuous_mul hU hG).integrable_of_hasCompactSupport h.2.1.mul_right

theorem IsTest.exists_transpose (hU : IsOpen U) (h : IsTest U α) (L : V →L[ℝ] V) :
    ∃ β, IsTest U β ∧ ∀ G : V → ℂ, ContDiffOn ℝ ∞ G U →
      ∫ x, α x * _root_.fderiv ℝ G x (L x) ∂ν = ∫ x, β x * G x ∂ν := by
  let b := Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => α x * (b.repr (L x) i : ℝ)
  have hc : ∀ i, IsTest U (c i) := fun i => h.mul (Complex.ofRealCLM.contDiff.comp
    ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp L.contDiff))
  refine ⟨∑ i, fun x => _root_.fderiv ℝ (c i) x (b i) * (-1), isTest_sum _ fun i => ((hc i).fderiv _).mul contDiff_const,
    fun G hG => ?_⟩
  have hG' : ∀ v, ContinuousOn (fun x => _root_.fderiv ℝ G x v) U := fun v =>
    (hG.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have e : ∀ x, α x * _root_.fderiv ℝ G x (L x) = ∑ i, c i x * _root_.fderiv ℝ G x (b i) := fun x => by
    conv_lhs => rw [← b.sum_repr (L x)]
    simp only [map_sum, map_smul, Finset.mul_sum, c, Complex.real_smul, mul_assoc]
  simp only [e, Finset.sum_apply, Finset.sum_mul]
  rw [integral_finset_sum _ fun i _ => (hc i).integrable_mul ν hU (hG' _), integral_finset_sum _ fun i _ =>
    (((hc i).fderiv _).mul contDiff_const).integrable_mul ν hU hG.continuousOn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (((hc i).fderiv _).integrable_mul ν hU hG.continuousOn)
    ((hc i).integrable_mul ν hU (hG' _)) ((hc i).integrable_mul ν hU hG.continuousOn)
    (fun x _ => (hc i).1.differentiable (by simp) x)
    (fun x hx => (hG.contDiffAt (hU.mem_nhds ((hc i).2.2 hx))).differentiableAt (by simp)), ← integral_neg]
  congr 1; funext x; ring

end Test

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (φ : GA E a → ℂ) (x : GA E a) : ℂ :=
  ∫ y, α y * chart φ x y ∂ν

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

def weakIn (S : Submodule ℂ (L2 (latticeGL E a) μ)) : Submodule ℂ (Sm E a) where
  carrier := {φ | ∀ (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α, IsTest (invSet E a) α →
    ∃ F ∈ S, lift (latticeGL E a) F =ᵐ[μ] smoothing ν α φ.1}
  zero_mem' ν _ α _ := ⟨0, zero_mem _, (ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)).mono fun x e =>
    e.trans (by simp [smoothing, chart])⟩
  add_mem' {φ ψ} h h' ν hν α hα := by
    obtain ⟨F, h1, e⟩ := h ν hν α hα
    obtain ⟨F', h2, e'⟩ := h' ν hν α hα
    refine ⟨F + F', add_mem h1 h2, Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F'))
      ((e.add e').trans (.of_forall fun x => ?_))⟩
    refine (integral_add (hα.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hα.integrable_mul ν isOpen_invSet (ψ.2 x).continuousOn)).symm.trans ?_
    refine integral_congr_ae (.of_forall fun y => ?_)
    by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_add]
  smul_mem' c φ h ν hν α hα := by
    obtain ⟨F, h1, e⟩ := h ν hν α hα
    refine ⟨c • F, S.smul_mem c h1, Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F))
      ((e.const_smul c).trans (.of_forall fun x => ?_))⟩
    refine (integral_const_mul c _).symm.trans (integral_congr_ae (.of_forall fun y => ?_))
    by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_left_comm]

omit [IsTotallyComplex E] in

def rmulEquiv (k : GL (Fin a) (Cinf E)) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse (rmul (toL k.val)) (rmul (toL (k⁻¹).val))
    (fun x => k.mul_inv_cancel_right (Matrix.of x)) fun x => k.inv_mul_cancel_right (Matrix.of x)

variable {μ} [μ.IsMulRightInvariant] {S : Submodule ℂ (L2 (latticeGL E a) μ)}

theorem isStable_weakIn (hS : IsSubrep (R (latticeGL E a) μ) S) : IsStable (weakIn μ S) := by
  intro o φ h ν hν α hα
  cases o with
  | fin k =>
    obtain ⟨F, h1, e⟩ := h ν hν α hα
    refine ⟨_, hS.2 (finGL E a k) F h1, (lift_R _ F).trans (Filter.EventuallyEq.trans
      ((measurePreserving_mul_right μ _).quasiMeasurePreserving.ae e) (.of_forall fun x => ?_))⟩
    exact congrArg (fun f => ∫ y, α y * f y ∂ν) (chart_rt_fin φ.1 x k).symm
  | cpt k =>
    let L := rmulEquiv (Unitary.toUnits k : GL (Fin a) (Cinf E))
    obtain ⟨F, h1, e⟩ := h (ν.map L) (L.isAddHaarMeasure_map ν) (α ∘ L.symm) ⟨hα.1.comp L.symm.contDiff,
      hα.2.1.comp_homeomorph L.symm.toHomeomorph, fun y hy => by
        have h2 : L.symm y ∈ invSet E a :=
          hα.2.2 ((Set.ext_iff.1 (tsupport_comp_eq_preimage α L.symm.toHomeomorph) y).1 hy)
        exact (Units.isUnit_mul_units _ (Unitary.toUnits k)⁻¹).1 h2⟩
    refine ⟨F, h1, e.trans (.of_forall fun x => ?_)⟩
    refine (L.toHomeomorph.measurableEmbedding.integral_map _).trans ?_
    refine integral_congr_ae (.of_forall fun y => ?_)
    exact congrArg₂ (· * ·) (congrArg α (L.symm_apply_apply y)) (congrFun (chart_rt_inf φ.1 x _) y).symm
  | lie X =>
    obtain ⟨β, hβ, e'⟩ := hα.exists_transpose ν isOpen_invSet (rmul X)
    obtain ⟨F, h1, e⟩ := h ν hν β hβ
    refine ⟨F, h1, e.trans (.of_forall fun x => ?_)⟩
    refine (e' _ (φ.2 x)).symm.trans (integral_congr_ae (.of_forall fun y => ?_))
    by_cases hy : y ∈ invSet E a
    · exact congrArg (α y * ·) (chart_lieD φ.2 X x hy).symm
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hα.2.2 h)
      simp [this]

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in
theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin a) (Cinf E) → Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact Units.isOpenEmbedding_val
end

theorem continuous_infGL : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Continuous fun p : GA E a × Lie E a => α p.2 * chart φ p.1 p.2 := by
  refine continuous_of_tsupport fun p hp => (hα.1.continuous.comp continuous_snd).continuousAt.mul ?_
  have h1 : p.2 ∈ tsupport α := by
    refine (closure_minimal (fun q hq => ?_) ((isClosed_tsupport α).preimage continuous_snd) :
      _ ⊆ Prod.snd ⁻¹' tsupport α) hp
    exact subset_tsupport _ (left_ne_zero_of_mul hq)
  obtain ⟨x, y⟩ := p
  obtain ⟨u, hu⟩ := hα.2.2 h1
  obtain rfl : y = toL u.val := hu.symm
  have he : IsOpenEmbedding (Prod.map id fun u : GL (Fin a) (Cinf E) => toL u.val : GA E a × _ → GA E a × Lie E a) :=
    IsOpenEmbedding.id.prodMap isOpenEmbedding_val
  refine (he.continuousAt_iff (x := (x, u))).1 (Continuous.continuousAt ?_)
  exact (hφ.comp (continuous_fst.mul (continuous_infGL.comp continuous_snd))).congr fun q => (chart_val φ q.1 q.2).symm

theorem norm_chart_le {φ : GA E a → ℂ} {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (x : GA E a) (y : Lie E a) : ‖chart φ x y‖ ≤ C := by
  unfold chart
  split_ifs
  · exact hC _
  · exact norm_zero.trans_le ((norm_nonneg _).trans (hC 1))

theorem continuous_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) :
    Continuous (smoothing ν α φ) :=
  continuous_of_dominated (bound := fun y => ‖α y‖ * C)
    (fun x => ((continuous_integrand hα hφ).comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun x => .of_forall fun y => (norm_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (norm_chart_le hC x y) (norm_nonneg _)))
    ((hα.1.continuous.integrable_of_hasCompactSupport hα.2.1).norm.mul_const C)
    (.of_forall fun y => (continuous_integrand hα hφ).comp (Continuous.prodMk_left y))

variable [IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)]

omit [μ.IsMulRightInvariant] in

theorem memL2_of_bound {φ : GA E a → ℂ} (hφ : Continuous φ) (hl : LeftInv (latticeGL E a) φ) {C : ℝ}
    (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ :=
  ⟨hl, MemLp.of_bound (aestronglyMeasurable_quotMeasure_iff_lift.2 (by
    rw [hl.lift_descend]; exact hφ.aestronglyMeasurable)) C (.of_forall fun q => hC _)⟩

theorem mem_weakIn (hS : IsSubrep (R (latticeGL E a) μ) S) {φ : Sm E a} (hφ : Continuous φ.1)
    (hl : LeftInv (latticeGL E a) φ.1) {C : ℝ} (hC : ∀ g, ‖φ.1 g‖ ≤ C) {F : L2 (latticeGL E a) μ} (hF : F ∈ S)
    (e : lift (latticeGL E a) F =ᵐ[μ] φ.1) : φ ∈ weakIn μ S := by
  intro ν hν α hα
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have : SigmaFinite ν := Measure.IsAddHaarMeasure.sigmaFinite ν
  have hαi : Integrable α ν := hα.1.continuous.integrable_of_hasCompactSupport hα.2.1
  have hm : MemL2Quotient (latticeGL E a) μ (smoothing ν α φ.1) :=
    memL2_of_bound (C := ∫ y, ‖α y‖ * C ∂ν) (continuous_smoothing ν hα hφ hC)
      (fun γ hγ g => by simp only [smoothing, chart, mul_assoc, hl γ hγ])
      fun g => norm_integral_le_of_norm_le (hαi.norm.mul_const C) (.of_forall fun y => (norm_mul _ _).trans_le
        (mul_le_mul_of_nonneg_left (norm_chart_le hC g y) (norm_nonneg _)))
  refine ⟨hm.toL2, ?_, hm.lift_toL2_ae_eq⟩
  have := hS.completeSpace
  rw [← S.orthogonal_orthogonal]
  intro y hy
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  have hyi : Integrable (fun g => conj (lift (latticeGL E a) y g)) (μ.restrict (stdDom (latticeGL E a))) := by
    have h1 : Integrable (fun q => conj (y q)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) :=
      (Lp.memLp y).star.integrable one_le_two
    exact (measurePreserving_mk hD).integrable_comp_of_integrable h1
  have key : ∀ {G : L2 (latticeGL E a) μ} {ψ : GA E a → ℂ}, lift (latticeGL E a) G =ᵐ[μ] ψ →
      ⟪y, G⟫_ℂ = ∫ g in stdDom (latticeGL E a), conj (lift (latticeGL E a) y g) * ψ g ∂μ := by
    intro G ψ h
    rw [MeasureTheory.L2.inner_def, integral_quotMeasure hD]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with g e
    rw [← e, RCLike.inner_apply']
    rfl
  have hi : Integrable (fun p : GA E a × Lie E a => conj (lift (latticeGL E a) y p.1) * (α p.2 * chart φ.1 p.1 p.2))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((hyi.norm.mul_prod hαi.norm).mul_const C).mono'
      (hyi.1.comp_fst.mul (continuous_integrand hα hφ).aestronglyMeasurable) (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_chart_le hC _ _) (norm_nonneg _)) (norm_nonneg _)
  rw [key hm.lift_toL2_ae_eq]
  simp only [smoothing, ← integral_const_mul]
  rw [integral_integral_swap hi]
  refine integral_eq_zero_of_ae (.of_forall fun M => ?_)
  by_cases hM : M ∈ invSet E a
  · obtain ⟨u, hu⟩ := hM
    obtain rfl : M = toL u.val := hu.symm
    simp only [chart_val, mul_left_comm _ (α _), integral_const_mul]
    rw [← key ((lift_R _ F).trans ((measurePreserving_mul_right μ _).quasiMeasurePreserving.ae e)),
      (S.mem_orthogonal' y).1 hy _ (hS.2 _ F hF), mul_zero]
    rfl
  · have : α M = 0 := image_eq_zero_of_notMem_tsupport fun h => hM (hα.2.2 h)
    simp [this]

omit [μ.IsMulRightInvariant] [IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)] in

theorem eq_zero_of_mem_weakIn {φ : Sm E a} (hφ : Continuous φ.1) {C : ℝ} (hC : ∀ g, ‖φ.1 g‖ ≤ C)
    (h : φ ∈ weakIn μ S) (h' : φ ∈ weakIn μ Sᗮ) : φ = 0 := by
  refine Subtype.ext (funext fun x => ?_)
  let ν : Measure (Lie E a) := Measure.addHaar
  have h1 := isOpen_invSet.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := ν) (f := chart φ.1 x)
    ((φ.2 x).continuousOn.locallyIntegrableOn isOpen_invSet.measurableSet) fun β b1 b2 b3 => by
      have hα : IsTest (invSet E a) fun y => (β y : ℂ) :=
        ⟨Complex.ofRealCLM.contDiff.comp b1, b2.comp_left (g := Complex.ofReal) rfl,
          (tsupport_comp_subset (g := Complex.ofReal) rfl β).trans b3⟩
      obtain ⟨F, h1, e⟩ := h ν inferInstance _ hα
      obtain ⟨F', h2, e'⟩ := h' ν inferInstance _ hα
      obtain rfl : F = F' := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans e'.symm)
      obtain rfl : F = 0 := inner_self_eq_zero.1 (h2 F h1)
      have := (Continuous.ae_eq_iff_eq μ (continuous_smoothing ν hα hφ hC) continuous_zero).1
        (e.symm.trans (ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)))
      exact congrFun this x
  have h2 : Set.EqOn (chart φ.1 x) 0 (invSet E a) :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' isOpen_invSet.measurableSet).2 h1) isOpen_invSet
      (φ.2 x).continuousOn continuousOn_const
  have h3 := (chart_val φ.1 x 1).symm.trans (h2 (val_mem_invSet 1))
  rwa [map_one, mul_one] at h3

end GlobalTheory.CuspQuot

end
