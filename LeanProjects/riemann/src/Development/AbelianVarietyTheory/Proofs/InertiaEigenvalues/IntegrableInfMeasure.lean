import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology

namespace GlobalTheory.RSThetaLow

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_invT {R : Type} [CommRing R] [TopologicalSpace R] : Continuous (invT a R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invT_invT {R : Type} [CommRing R] (g : GL (Fin a) R) : invT a R (invT a R g) = g :=
  Units.ext (transpose_transpose _)

theorem decays_invT_smoothInf {F : GA E a → ℂ} (hF : Decays fun g => F (invT a (Ad E) g)) {f : Lie E a → ℂ}
    (hf : IsTest (invSet E a) f) : Decays fun g => GlobalTheory.JSW.smoothInf f F (invT a (Ad E) g) := by
  intro L hL C₀ hC₀ N
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' tsupport f) :=
    isOpenEmbedding_val.isInducing.isCompact_preimage' hf.2.1 fun x hx => hf.2.2 hx
  obtain ⟨C, h⟩ := hF L hL _ (hC₀.mul ((hK.image continuous_infGL).image continuous_invT)) N
  have hi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  refine ⟨(∫ x, ‖f x‖) * C, fun g c hcC ξ hξ hm => ?_⟩
  rw [mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hi.norm.mul_const _) (.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport f
  · obtain ⟨u, hu⟩ := hf.2.2 hx
    obtain rfl : x = toL u.val := hu.symm
    rw [norm_mul, chart_val]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := h g _ (Set.mul_mem_mul hcC ⟨_, ⟨u, hx, rfl⟩, rfl⟩) ξ hξ hm
    simpa only [map_mul, invT_invT, mul_assoc] using h1
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem decays_invT {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ withSmoothings π) :
    Decays fun g => φ.1 (invT a (Ad E) g) := by
  let D : Submodule ℂ (Sm E a) :=
    { carrier := {φ | Decays fun g => φ.1 (invT a (Ad E) g)}
      add_mem' := fun {φ ψ} h h' => Decays.add (F := fun g => φ.1 (invT a (Ad E) g)) (G := fun g => ψ.1 (invT a (Ad E) g)) h h'
      zero_mem' := Decays.zero
      smul_mem' := fun z φ h => Decays.smul (F := fun g => φ.1 (invT a (Ad E) g)) h z }
  have h0 : π.V ≤ D := fun ψ hψ =>
    decays_of_mem (CuspSub.IsUnitary.contra hπ) (φ := UpperTheory.V.TC.dualFn E a ψ) ⟨ψ, hψ, rfl⟩
  refine (sup_le h0 (Submodule.span_le.2 ?_) : withSmoothings π ≤ D) hφ
  rintro F ⟨f, ψ, hf, hψ, e⟩
  change Decays fun g => F.1 (invT a (Ad E) g)
  rw [e]
  exact decays_invT_smoothInf (h0 hψ) hf

theorem continuous_bounded {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ withSmoothings π) :
    Continuous φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  obtain ⟨χ, hω, h⟩ := hπ
  have := mem_bddForms_of_withSmoothings (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
    (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)) hω (CuspSub.hasCentral_iff.1 h) hφ
  exact ⟨this.1, this.2.2.2⟩

omit [IsTotallyComplex E] in

def rowInv (ℓ : Fin a) (y : Fin a → Cinf E) : Lie E a := invL (toL (rowMat ℓ y))

omit [IsTotallyComplex E] in
theorem contDiff_rowMat (ℓ : Fin a) : ContDiff ℝ ∞ fun y : Fin a → Cinf E => toL (rowMat ℓ y) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i = ℓ
  · subst h
    have : (fun y : Fin a → Cinf E => toL (rowMat i y) i) = id := funext fun y => updateRow_self
    rw [this]; exact contDiff_id
  · have : (fun y : Fin a → Cinf E => toL (rowMat ℓ y) i) = fun _ => (1 : Matrix (Fin a) (Fin a) (Cinf E)) i :=
      funext fun y => updateRow_ne h
    rw [this]; exact contDiff_const

omit [IsTotallyComplex E] in
theorem contDiffAt_rowInv {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) : ContDiffAt ℝ ∞ (rowInv ℓ) y :=
  (contDiffAt_invL (isUnit_rowMat_iff.2 (isUnit_of_mem_rowSet hy))).comp y (contDiff_rowMat ℓ).contDiffAt

omit [IsTotallyComplex E] in
theorem rowInv_eq {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) : rowInv ℓ y = toL ((rowGL ℓ y)⁻¹).val := by
  rw [rowInv, ← val_rowGL (isUnit_of_mem_rowSet hy), invL_val]

theorem chart_rowInv (F : GA E a → ℂ) (g : GA E a) {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) :
    F (g * (infGL E a (rowGL ℓ y))⁻¹) = chart F g (rowInv ℓ y) := by
  rw [rowInv_eq hy, chart_val, map_inv]

theorem contDiffAt_translate (F : Sm E a) (g : GA E a) {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ) :
    ContDiffAt ℝ ∞ (fun y => F.1 (g * (infGL E a (rowGL ℓ y))⁻¹)) y :=
  ((contDiffAt_chart F.2 g (rowInv_eq hy ▸ val_mem_invSet _)).comp y (contDiffAt_rowInv hy)).congr_of_eventuallyEq
    (Filter.eventually_of_mem ((isOpen_rowSet ℓ).mem_nhds hy) fun _ hz => chart_rowInv _ g hz)

omit [IsTotallyComplex E] in

def rowCoef (ℓ : Fin a) (v : Fin a → Cinf E) (β : Fin (Module.finrank ℝ (Lie E a))) (y : Fin a → Cinf E) : ℂ :=
  ((Module.finBasis ℝ (Lie E a)).coord β (toL (rowMat ℓ y * Matrix.of (fderiv ℝ (rowInv ℓ) y v))) : ℝ)

omit [IsTotallyComplex E] in
theorem contDiffOn_rowCoef (ℓ : Fin a) (v : Fin a → Cinf E) (β : Fin (Module.finrank ℝ (Lie E a))) :
    ContDiffOn ℝ ∞ (rowCoef ℓ v β) (rowSet E ℓ) := fun y hy => by
  refine ContDiffAt.contDiffWithinAt (Complex.ofRealCLM.contDiff.contDiffAt.comp y
    ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord β)).contDiff.contDiffAt.comp y ?_))
  have h1 : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (rowInv ℓ) y v) y :=
    ((contDiffAt_rowInv hy).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  have h2 := (contDiff_rowMat (E := E) ℓ).contDiffAt (x := y)
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  change ContDiffAt ℝ ∞ (fun y => ∑ k, toL (rowMat ℓ y) i k * fderiv ℝ (rowInv ℓ) y v k j) y
  exact ContDiffAt.sum fun k _ => (contDiffAt_pi.1 (contDiffAt_pi.1 h2 i) k).mul
    (contDiffAt_pi.1 (contDiffAt_pi.1 h1 k) j)

theorem fderiv_translate (F : Sm E a) (g : GA E a) {ℓ : Fin a} {y : Fin a → Cinf E} (hy : y ∈ rowSet E ℓ)
    (v : Fin a → Cinf E) : fderiv ℝ (fun y => F.1 (g * (infGL E a (rowGL ℓ y))⁻¹)) y v =
      ∑ β, rowCoef ℓ v β y * (lie E a (Module.finBasis ℝ (Lie E a) β) F).1 (g * (infGL E a (rowGL ℓ y))⁻¹) := by
  have hm : rowInv ℓ y ∈ invSet E a := rowInv_eq hy ▸ val_mem_invSet _
  have e : (fun y => F.1 (g * (infGL E a (rowGL ℓ y))⁻¹)) =ᶠ[𝓝 y] chart F.1 g ∘ rowInv ℓ :=
    Filter.eventually_of_mem ((isOpen_rowSet ℓ).mem_nhds hy) fun _ hz => chart_rowInv _ g hz
  set X : Lie E a := toL (rowMat ℓ y * Matrix.of (fderiv ℝ (rowInv ℓ) y v)) with hX
  have h1 : rmul X (rowInv ℓ y) = fderiv ℝ (rowInv ℓ) y v := by
    rw [rowInv_eq hy, hX, ← val_rowGL (isUnit_of_mem_rowSet hy)]
    exact Units.inv_mul_cancel_left (rowGL ℓ y) (Matrix.of (fderiv ℝ (rowInv ℓ) y v))
  rw [e.fderiv_eq, fderiv_comp _ ((contDiffAt_chart F.2 g hm).differentiableAt (by simp))
    ((contDiffAt_rowInv hy).differentiableAt (by simp)), ContinuousLinearMap.comp_apply, ← h1, ← chart_lieD F.2 X g hm,
    ← chart_rowInv _ g hy]
  change fderiv ℝ (chart F.1 _) (oneL E a) X = _
  conv_lhs => rw [← (Module.finBasis ℝ (Lie E a)).sum_repr X, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Complex.real_smul]
  rfl

theorem isTest_rsInf {ℓ : Fin a} (F F' : Sm E a) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    IsTest (rowSet E ℓ) (rsInf ℓ F.1 F'.1 Φ g) := by
  have hs : tsupport (rsInf ℓ F.1 F'.1 Φ g) ⊆ tsupport Φ := tsupport_mul_subset_right
  refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hΦ.2.1.mul_left, hs.trans hΦ.2.2⟩
  by_cases hy : y ∈ tsupport Φ
  · exact ((contDiffAt_translate F g (hΦ.2.2 hy)).mul (Complex.conjCLE.contDiff.contDiffAt.comp y
      (contDiffAt_translate F' g (hΦ.2.2 hy)))).mul hΦ.1.contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hs h))

theorem fderiv_rsInf {ℓ : Fin a} (F F' : Sm E a) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (g : GA E a)
    (y v : Fin a → Cinf E) : fderiv ℝ (rsInf ℓ F.1 F'.1 Φ g) y v =
      ∑ β, rsInf ℓ (lie E a (Module.finBasis ℝ (Lie E a) β) F).1 F'.1 (fun y => rowCoef ℓ v β y * Φ y) g y +
      ∑ β, rsInf ℓ F.1 (lie E a (Module.finBasis ℝ (Lie E a) β) F').1 (fun y => rowCoef ℓ v β y * Φ y) g y +
      rsInf ℓ F.1 F'.1 (fun y => fderiv ℝ Φ y v) g y := by
  by_cases hy : y ∈ tsupport Φ
  · have h1 := ((contDiffAt_translate F g (hΦ.2.2 hy)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((contDiffAt_translate F' g (hΦ.2.2 hy)).differentiableAt (by simp)).hasFDerivAt
    have h3 := (hΦ.1.differentiable (by simp) y).hasFDerivAt
    have h4 := ((h1.mul (Complex.conjCLE.hasFDerivAt.comp y h2)).mul h3).fderiv
    refine (congrArg (· v) h4).trans ?_
    have hc : ∀ β, conj (rowCoef ℓ v β y) = rowCoef ℓ v β y := fun β => Complex.conj_ofReal _
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      fderiv_translate _ g (hΦ.2.2 hy), rsInf, smul_eq_mul, Pi.mul_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_sum, map_mul, hc, Finset.mul_sum, mul_add]
    rw [add_comm, add_comm (∑ _, _)]
    congr 2 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  · have h0 : Φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h1 : fderiv ℝ Φ y = 0 := by
      rw [(notMem_tsupport_iff_eventuallyEq.1 hy).fderiv_eq]; simp
    have h2 : fderiv ℝ (rsInf ℓ F.1 F'.1 Φ g) y = 0 := by
      have hs : tsupport (rsInf ℓ F.1 F'.1 Φ g) ⊆ tsupport Φ := tsupport_mul_subset_right
      rw [(notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hs h)).fderiv_eq]
      simp
    rw [h2]
    simp [rsInf, h0, h1]

omit [IsTotallyComplex E] in
theorem isTest_rowCoef_mul {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : IsTest (rowSet E ℓ) Φ) (v : Fin a → Cinf E)
    (β : Fin (Module.finrank ℝ (Lie E a))) : IsTest (rowSet E ℓ) fun y => rowCoef ℓ v β y * Φ y := by
  have hs : tsupport (fun y => rowCoef ℓ v β y * Φ y) ⊆ tsupport Φ := tsupport_mul_subset_right
  refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hΦ.2.1.mul_left, hs.trans hΦ.2.2⟩
  by_cases hy : y ∈ tsupport Φ
  · exact ((contDiffOn_rowCoef ℓ v β).contDiffAt ((isOpen_rowSet ℓ).mem_nhds (hΦ.2.2 hy))).mul hΦ.1.contDiffAt
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hs h))

omit [IsTotallyComplex E] in
theorem integrable_infMeasure {f : (Fin a → Cinf E) → ℂ} (h : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (infMeasure E a) :=
  (h.integrable_of_hasCompactSupport hc).smul_measure (by simp)

def famSpan {ι : Type} (ℓ : Fin a) (S S' : Submodule ℂ (Sm E a)) (g : ι → GA E a) :
    Submodule ℂ (ι → (Fin a → Cinf E) → ℂ) :=
  Submodule.span ℂ {f | ∃ F ∈ S, ∃ F' ∈ S', ∃ Φ, IsTest (rowSet E ℓ) Φ ∧ f = fun i => rsInf ℓ F.1 F'.1 Φ (g i)}

theorem famSpan_bound {ι : Type} {ℓ : Fin a} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a} {w : ι → ℝ}
    (hS : ∀ F ∈ S, ∀ C₀ : Set (GA E a), IsCompact C₀ → ∃ C : ℝ, ∀ i, ∀ c ∈ C₀, ‖F.1 (g i * c)‖ ≤ C * w i)
    (hS' : ∀ F ∈ S', ∃ C : ℝ, ∀ x, ‖F.1 x‖ ≤ C) : ∀ f ∈ famSpan ℓ S S' g,
      (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E a) ≤ C * w i := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, F', hF', Φ, hΦ, rfl⟩ := hf
    refine ⟨fun i => ⟨(isTest_rsInf F F' hΦ _).1, (isTest_rsInf F F' hΦ _).2.1⟩, ?_⟩
    obtain ⟨C, hC⟩ := hS F hF _ (hΦ.2.1.isCompact.image_of_continuousOn ((continuousOn_inv_rowGL ℓ).mono hΦ.2.2))
    obtain ⟨D, hD⟩ := hS' F' hF'
    refine ⟨(∫ y, ‖Φ y‖ ∂(infMeasure E a)) * (D * C), fun i => ?_⟩
    rw [mul_assoc, ← integral_mul_const]
    refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _)
      ((integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.mul_const _) (.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport Φ
    · have h1 := hC i _ ⟨y, hy, rfl⟩
      simp only [rsInf, norm_mul, Complex.norm_conj]
      rw [mul_comm, mul_assoc D, mul_comm D]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (hD _) (norm_nonneg _) ((norm_nonneg _).trans h1)) (norm_nonneg _)
    · simp [rsInf, image_eq_zero_of_notMem_tsupport hy]
  | zero => exact ⟨fun i => ⟨contDiff_const, HasCompactSupport.zero⟩, 0, fun i => by simp⟩
  | add f f' _ _ h h' =>
    obtain ⟨h1, C, h2⟩ := h
    obtain ⟨h1', C', h2'⟩ := h'
    refine ⟨fun i => ⟨(h1 i).1.add (h1' i).1, (h1 i).2.add (h1' i).2⟩, C + C', fun i => ?_⟩
    have k := (integrable_infMeasure (h1 i).1.continuous (h1 i).2).norm
    have k' := (integrable_infMeasure (h1' i).1.continuous (h1' i).2).norm
    rw [add_mul]
    refine le_trans ?_ (add_le_add (h2 i) (h2' i))
    rw [← integral_add k k']
    exact integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (k.add k') (.of_forall fun y => norm_add_le _ _)
  | smul z f _ h =>
    obtain ⟨h1, C, h2⟩ := h
    refine ⟨fun i => ⟨(h1 i).1.const_smul z, (h1 i).2.smul_left (f := fun _ => z)⟩, ‖z‖ * C, fun i => ?_⟩
    simp only [Pi.smul_apply, norm_smul, integral_const_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 i) (norm_nonneg _)

theorem famSpan_fderiv {ι : Type} {ℓ : Fin a} {S S' : Submodule ℂ (Sm E a)} {g : ι → GA E a}
    (hS : ∀ X, ∀ F ∈ S, lie E a X F ∈ S) (hS' : ∀ X, ∀ F ∈ S', lie E a X F ∈ S') : ∀ f ∈ famSpan ℓ S S' g,
      (∀ i, Differentiable ℝ (f i)) ∧ ∀ v, (fun i y => fderiv ℝ (f i) y v) ∈ famSpan ℓ S S' g := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨F, hF, F', hF', Φ, hΦ, rfl⟩ := hf
    refine ⟨fun i => (isTest_rsInf F F' hΦ _).1.differentiable (by simp), fun v => ?_⟩
    have e : (fun i y => fderiv ℝ (rsInf ℓ F.1 F'.1 Φ (g i)) y v) =
        ∑ β, (fun i => rsInf ℓ (lie E a (Module.finBasis ℝ (Lie E a) β) F).1 F'.1
          (fun y => rowCoef ℓ v β y * Φ y) (g i)) +
        ∑ β, (fun i => rsInf ℓ F.1 (lie E a (Module.finBasis ℝ (Lie E a) β) F').1
          (fun y => rowCoef ℓ v β y * Φ y) (g i)) +
        fun i => rsInf ℓ F.1 F'.1 (fun y => fderiv ℝ Φ y v) (g i) := by
      funext i y
      simp only [Pi.add_apply, Finset.sum_apply]
      exact fderiv_rsInf F F' hΦ _ y v
    rw [e]
    exact add_mem (add_mem
      (Submodule.sum_mem _ fun β _ => Submodule.subset_span ⟨_, hS _ F hF, F', hF', _, isTest_rowCoef_mul hΦ v β, rfl⟩)
      (Submodule.sum_mem _ fun β _ => Submodule.subset_span ⟨F, hF, _, hS' _ F' hF', _, isTest_rowCoef_mul hΦ v β, rfl⟩))
      (Submodule.subset_span ⟨F, hF, F', hF', _, hΦ.fderiv v, rfl⟩)
  | zero =>
    refine ⟨fun i => differentiable_const _, fun v => ?_⟩
    convert zero_mem (famSpan ℓ S S' g) using 1
    funext i y
    simp
  | add f f' _ _ h h' =>
    refine ⟨fun i => (h.1 i).add (h'.1 i), fun v => ?_⟩
    convert add_mem (h.2 v) (h'.2 v) using 1
    funext i y
    rw [Pi.add_apply, fderiv_add (h.1 i y) (h'.1 i y)]
    rfl
  | smul z f _ h =>
    refine ⟨fun i => (h.1 i).const_smul z, fun v => ?_⟩
    convert Submodule.smul_mem _ z (h.2 v) using 1
    funext i y
    rw [Pi.smul_apply, fderiv_const_smul (h.1 i y)]
    rfl

end GlobalTheory.RSThetaLow
