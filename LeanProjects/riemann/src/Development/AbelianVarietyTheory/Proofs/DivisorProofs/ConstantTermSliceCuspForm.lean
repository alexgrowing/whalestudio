import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwoSmooth

open Topology Filter
open scoped ContDiff

section General

variable {X P : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in

theorem iteratedFDeriv_fderiv_eq' {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : P → F) (m : ℕ) (x : P) :
    iteratedFDeriv ℝ m (fderiv ℝ f) x =
      (continuousMultilinearCurryRightEquiv' ℝ m P F) (iteratedFDeriv ℝ (m + 1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

omit [MeasurableSpace X] [OpensMeasurableSpace X] [FiniteDimensional ℝ P] in

theorem continuousOn_of_iteratedFDeriv_zero {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : X → P → F}
    {s : Set (X × P)} (h : ContinuousOn (fun p : X × P => iteratedFDeriv ℝ 0 (H p.1) p.2) s) :
    ContinuousOn (fun p : X × P => H p.1 p.2) s := by
  have e : (fun p : X × P => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ P F (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]
  exact (continuousMultilinearCurryFin0 ℝ P F).continuous.comp_continuousOn h

theorem hasFDerivAt_integral_param (ν : Measure X) [IsFiniteMeasure ν] {U : Set P} (hU : IsOpen U) {S : Set X}
    (hS : IsCompact S) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (H : X → P → F)
    (hrep : ∀ u, ∃ v ∈ S, H u = H v) (hd : ∀ u, DifferentiableOn ℝ (H u) U)
    (h0 : ContinuousOn (fun p : X × P => H p.1 p.2) (Set.univ ×ˢ U))
    (h1 : ContinuousOn (fun p : X × P => fderiv ℝ (H p.1) p.2) (Set.univ ×ˢ U)) {x₀ : P} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ u, H u x ∂ν) (∫ u, fderiv ℝ (H u) x₀ ∂ν) x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hcb : Metric.closedBall x₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (S ×ˢ Metric.closedBall x₀ (ε / 2)) := hS.prod (isCompact_closedBall _ _)
  have hsub : S ×ˢ Metric.closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ U := Set.prod_mono (Set.subset_univ _) hcb
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn (h0.mono hsub)
  have bd : ∀ u, ∀ x ∈ Metric.closedBall x₀ (ε / 2), ‖fderiv ℝ (H u) x‖ ≤ C := fun u x hx => by
    obtain ⟨v, hv, e⟩ := hrep u
    rw [e]; exact hC (v, x) ⟨hv, hx⟩
  have bd0 : ∀ u, ‖H u x₀‖ ≤ C0 := fun u => by
    obtain ⟨v, hv, e⟩ := hrep u
    rw [e]; exact hC0 (v, x₀) ⟨hv, Metric.mem_closedBall_self (by linarith)⟩
  have hcx : ∀ x ∈ U, Continuous fun u => H u x := fun x hx =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun u => ⟨trivial, hx⟩
  have hcx' : Continuous fun u => fderiv ℝ (H u) x₀ :=
    h1.comp_continuous (continuous_id.prodMk continuous_const) fun u => ⟨trivial, hx₀⟩
  have hball2 : Metric.ball x₀ (ε / 2) ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ (by linarith)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hball2
    (Filter.eventually_of_mem (hU.mem_nhds hx₀) fun x hx => (hcx x hx).aestronglyMeasurable)
    (Integrable.of_bound (hcx x₀ hx₀).aestronglyMeasurable C0 (.of_forall bd0)) hcx'.aestronglyMeasurable
    (.of_forall fun u x hx => bd u x (Metric.ball_subset_closedBall hx)) (integrable_const C)
    (.of_forall fun u x hx =>
      ((hd u).differentiableAt (hU.mem_nhds (hcb (Metric.ball_subset_closedBall hx)))).hasFDerivAt)

theorem contDiffOn_integral_param (ν : Measure X) [IsFiniteMeasure ν] {U : Set P} (hU : IsOpen U) {S : Set X}
    (hS : IsCompact S) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (H : X → P → F),
      (∀ u, ∃ v ∈ S, H u = H v) → (∀ u, ContDiffOn ℝ ∞ (H u) U) →
      (∀ m : ℕ, ContinuousOn (fun p : X × P => iteratedFDeriv ℝ m (H p.1) p.2) (Set.univ ×ˢ U)) →
      ContDiffOn ℝ n (fun x => ∫ u, H u x ∂ν) U := by
  induction n with
  | zero =>
    intro F _ _ _ H hrep hs hm
    have h1 : ContinuousOn (fun p : X × P => fderiv ℝ (H p.1) p.2) (Set.univ ×ˢ U) := by
      refine continuousOn_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq']
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 P F).continuous.comp_continuousOn (hm 1)
    refine contDiffOn_zero.2 fun x hx => ?_
    exact (hasFDerivAt_integral_param ν hU hS H hrep (fun u => (hs u).differentiableOn (by simp))
      (continuousOn_of_iteratedFDeriv_zero (hm 0)) h1 hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro F _ _ _ H hrep hs hm
    have hm' : ∀ m : ℕ, ContinuousOn (fun p : X × P => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2)
        (Set.univ ×ˢ U) := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq']
      exact (continuousMultilinearCurryRightEquiv' ℝ m P F).continuous.comp_continuousOn (hm (m + 1))
    have hrep' : ∀ u, ∃ v ∈ S, fderiv ℝ (H u) = fderiv ℝ (H v) := fun u => by
      obtain ⟨v, hv, e⟩ := hrep u
      exact ⟨v, hv, by rw [e]⟩
    have hD := ih (fun u => fderiv ℝ (H u)) hrep' (fun u => (hs u).fderiv_of_isOpen hU (by simp)) hm'
    have hder : ∀ x ∈ U, HasFDerivAt (fun x => ∫ u, H u x ∂ν) (∫ u, fderiv ℝ (H u) x ∂ν) x := fun x hx =>
      hasFDerivAt_integral_param ν hU hS H hrep (fun u => (hs u).differentiableOn (by simp))
        (continuousOn_of_iteratedFDeriv_zero (hm 0))
        (continuousOn_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) hx
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).2
      ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, by simp,
        hD.congr fun x hx => (hder x hx).fderiv⟩

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [FiniteDimensional ℝ P] in

theorem contDiffAt_iteratedFDeriv_param {M F : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : M → P → F) {O : Set (M × P)}
    (hΦ : ∀ q ∈ O, ContDiffAt ℝ ∞ (Function.uncurry Φ) q) (m : ℕ) :
    ∀ q ∈ O, ContDiffAt ℝ ∞ (fun q : M × P => iteratedFDeriv ℝ m (Φ q.1) q.2) q := by
  induction m with
  | zero =>
    intro q hq
    have e : (fun q : M × P => iteratedFDeriv ℝ 0 (Φ q.1) q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ P F).symm (Function.uncurry Φ q) := by
      funext q; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [e]
    exact (continuousMultilinearCurryFin0 ℝ P F).symm.contDiff.contDiffAt.comp q (hΦ q hq)
  | succ m ih =>
    intro q hq
    have e : (fun q : M × P => iteratedFDeriv ℝ (m + 1) (Φ q.1) q.2) =
        fun q => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => P) F).symm
          (fderiv ℝ (fun z => iteratedFDeriv ℝ m (Φ q.1) z) q.2) := by
      funext q; rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [e]
    refine (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => P) F).symm.contDiff.contDiffAt.comp q ?_
    refine ContDiffAt.fderiv (f := fun (q : M × P) (z : P) => iteratedFDeriv ℝ m (Φ q.1) z) (g := Prod.snd)
      ?_ contDiffAt_snd le_rfl
    have hg : ContDiffAt ℝ ∞ (fun p : (M × P) × P => (p.1.1, p.2)) (q, q.2) :=
      (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
    exact (ih (q.1, q.2) hq).comp (q, q.2) hg

end General

section Specific

open GlobalTheory.LeviGA GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

omit [IsTotallyComplex E] in

theorem contDiff_mulL {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Lie E n × Lie E n => toL (Matrix.of p.1 * Matrix.of p.2)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun p : Lie E n × Lie E n => ∑ k, p.1 i k * p.2 k j
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply_apply ℝ (Cinf E) i k).comp contDiff_fst).mul
      ((contDiff_apply_apply ℝ (Cinf E) k j).comp contDiff_snd)

omit [IsTotallyComplex E] in

theorem contDiff_blkMat_entry (hr : r ≤ a) (i k : Fin a) :
    ContDiff ℝ ∞ (fun x : Lie E (a - r) => blkMat (Cinf E) hr (1, Matrix.of x) i k) := by
  change ContDiff ℝ ∞ (fun x : Lie E (a - r) => Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (Cinf E)) 0 0
    (Matrix.of x) ((blkEquiv hr).symm i) ((blkEquiv hr).symm k))
  rcases (blkEquiv hr).symm i with i | i <;> rcases (blkEquiv hr).symm k with k | k
  · simp only [Matrix.fromBlocks_apply₁₁]; exact contDiff_const
  · simp only [Matrix.fromBlocks_apply₁₂]; exact contDiff_const
  · simp only [Matrix.fromBlocks_apply₂₁]; exact contDiff_const
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact contDiff_apply_apply ℝ (Cinf E) i k

omit [IsTotallyComplex E] in

def blkA (hr : r ≤ a) (κ : Kinf E a) (x : Lie E (a - r)) : Lie E a :=
  toL (blkMat (Cinf E) hr (1, Matrix.of x) * κ.1)

omit [IsTotallyComplex E] in

theorem contDiff_blkA (hr : r ≤ a) (κ : Kinf E a) : ContDiff ℝ ∞ (blkA hr κ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun x : Lie E (a - r) => ∑ k, blkMat (Cinf E) hr (1, Matrix.of x) i k * κ.1 k j
  exact ContDiff.sum fun k _ => (contDiff_blkMat_entry hr i k).mul contDiff_const

omit [IsTotallyComplex E] in

theorem blkA_mem (hr : r ≤ a) (κ : Kinf E a) {x : Lie E (a - r)} (hx : x ∈ invSet E (a - r)) :
    blkA hr κ x ∈ invSet E a := by
  have h1 : IsUnit ((1 : Matrix (Fin r) (Fin r) (Cinf E)), Matrix.of x) := Prod.isUnit_iff.2 ⟨isUnit_one, hx⟩
  exact (h1.map (blkMat (Cinf E) hr)).mul (Unitary.toUnits κ).isUnit

theorem chart_slice [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) (g : GA E (a - r)) {x : Lie E (a - r)} (hx : x ∈ invSet E (a - r)) :
    chart (slice E μ 𝓕 hr φ m₁ t κ) g x =
      ∫ u in 𝓕, chart φ (unip u * (blkGL hr (m₁, g) * finGL E a t)) (blkA hr κ x) ∂μ := by
  obtain ⟨y, hy⟩ := hx
  have ex : x = toL y.val := by rw [hy]; rfl
  subst ex
  rw [chart_val]
  unfold slice
  congr 1
  funext u
  have e : blkA hr κ (toL y.val) = toL (blkGL hr (1, y) * Unitary.toUnits κ).val := rfl
  rw [e, chart_val, blkGL_mul_infGL]
  congr 1
  rw [map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
  simp only [mul_assoc]

theorem chart_unip_add {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g) (G : GA E a)
    {γ : BlockIx a r → Ad E} (hγ : γ ∈ ratN E a r) (u : BlockIx a r → Ad E) :
    chart φ (unip (γ + u) * G) = chart φ (unip u * G) := by
  obtain ⟨y, rfl⟩ := hγ
  have e : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y) =
      ratGL E a (unip y) := unip_algebraMap y
  funext x
  unfold chart
  split_ifs
  · rw [unip_add, e, mul_assoc, mul_assoc, hl]; simp only [mul_assoc]
  · rfl

end Specific

section Local

open GlobalTheory.LeviGA GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem eventually_chart_eq (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (G : GA E a)
    (u₀ : BlockIx a r → Ad E) :
    ∀ᶠ u in 𝓝 u₀, ∀ y, chart φ.1 (unip u * G) y = chart φ.1 (unip u₀ * G)
      (toL (Matrix.of (toL (Matrix.GeneralLinearGroup.map (pInf E) ((unip u₀ * G)⁻¹ * (unip u * G))).val) *
        Matrix.of y)) := by
  have hc : Continuous fun u : BlockIx a r → Ad E =>
      Matrix.GeneralLinearGroup.map (pFin E) ((unip u₀ * G)⁻¹ * (unip u * G)) :=
    (ContAut.continuous_map_pFin E a).comp (continuous_const.mul (CuspidalL2GL.continuous_unip.mul continuous_const))
  have hmem : {u : BlockIx a r → Ad E | finRep E a (Matrix.GeneralLinearGroup.map (pFin E)
      ((unip u₀ * G)⁻¹ * (unip u * G))) φ = φ} ∈ 𝓝 u₀ := by
    refine (hlev.preimage hc).mem_nhds ?_
    change finRep E a _ φ = φ
    simp
  filter_upwards [hmem] with u hu y
  set h₀ := unip u₀ * G
  set h := unip u * G
  set c := Matrix.GeneralLinearGroup.map (pInf E) (h₀⁻¹ * h)
  set k := Matrix.GeneralLinearGroup.map (pFin E) (h₀⁻¹ * h)
  have key : h = h₀ * finGL E a k * infGL E a c := by
    rw [mul_assoc, ← infGL_comm, infGL_mul_finGL, mul_inv_cancel_left]
  have hk : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hu
  rw [key, chart_mul, ← chart_rt_fin, hk]
  rfl

theorem continuousAt_iteratedFDeriv (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (hr : r ≤ a)
    (κ : Kinf E a) (G : GA E a) (m : ℕ) (u₀ : BlockIx a r → Ad E) {x₀ : Lie E (a - r)}
    (hx₀ : x₀ ∈ invSet E (a - r)) :
    ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E (a - r) =>
      iteratedFDeriv ℝ m (fun x => chart φ.1 (unip p.1 * G) (blkA hr κ x)) p.2) (u₀, x₀) := by
  set h₀ := unip u₀ * G
  let Cm : (BlockIx a r → Ad E) → Lie E a := fun u =>
    toL (Matrix.GeneralLinearGroup.map (pInf E) (h₀⁻¹ * (unip u * G))).val
  have hCm : Continuous Cm :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp
      (continuous_const.mul (CuspidalL2GL.continuous_unip.mul continuous_const)))
  have hC0 : Cm u₀ = oneL E a := by
    simp only [Cm, h₀, inv_mul_cancel, map_one]
    rfl
  let Φ₂ : Lie E a → Lie E (a - r) → ℂ := fun c x =>
    chart φ.1 h₀ (toL (Matrix.of c * Matrix.of (blkA hr κ x)))
  have hq : ContDiff ℝ ∞ (fun q : Lie E a × Lie E (a - r) => toL (Matrix.of q.1 * Matrix.of (blkA hr κ q.2))) :=
    contDiff_mulL.comp (contDiff_fst.prodMk ((contDiff_blkA hr κ).comp contDiff_snd))
  let O : Set (Lie E a × Lie E (a - r)) :=
    {q | toL (Matrix.of q.1 * Matrix.of (blkA hr κ q.2)) ∈ invSet E a}
  have hΦ : ∀ q ∈ O, ContDiffAt ℝ ∞ (Function.uncurry Φ₂) q := fun q hq' => by
    have e : Function.uncurry Φ₂ =
        chart φ.1 h₀ ∘ fun q : Lie E a × Lie E (a - r) => toL (Matrix.of q.1 * Matrix.of (blkA hr κ q.2)) := rfl
    rw [e]
    exact (contDiffAt_chart φ.2 h₀ hq').comp q hq.contDiffAt
  have hO : (oneL E a, x₀) ∈ O := by
    change toL (Matrix.of (toL 1) * Matrix.of (blkA hr κ x₀)) ∈ invSet E a
    simpa using blkA_mem hr κ hx₀
  have hΨ := (contDiffAt_iteratedFDeriv_param Φ₂ hΦ m (oneL E a, x₀) hO).continuousAt
  have hcomp : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E (a - r) =>
      iteratedFDeriv ℝ m (Φ₂ (Cm p.1)) p.2) (u₀, x₀) :=
    ContinuousAt.comp_of_eq (g := fun q : Lie E a × Lie E (a - r) => iteratedFDeriv ℝ m (Φ₂ q.1) q.2)
      (f := fun p : (BlockIx a r → Ad E) × Lie E (a - r) => (Cm p.1, p.2)) hΨ
      ((hCm.comp continuous_fst).prodMk continuous_snd).continuousAt (Prod.ext hC0 rfl)
  refine hcomp.congr ?_
  have hev := (continuous_fst.tendsto (u₀, x₀)).eventually (eventually_chart_eq φ hlev G u₀)
  filter_upwards [hev] with p hp
  have e : (fun x => chart φ.1 (unip p.1 * G) (blkA hr κ x)) = Φ₂ (Cm p.1) := funext fun x => hp _
  rw [e]

end Local

theorem slice_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a),
      GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ ∈ Sm E (a - r) := by
  intro E _ _ _ a r hr _ _ μ 𝓕 _ _ h1 φ hφ m₁ t κ g
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  set G := GlobalTheory.LeviGA.blkGL hr (m₁, g) * finGL E a t
  let H : (BlockIx a r → Ad E) → Lie E (a - r) → ℂ := fun u x => chart φ.1 (unip u * G) (blkA hr κ x)
  have hrep : ∀ u, ∃ v ∈ K, H u = H v := fun u => by
    obtain ⟨γ, hγ, hk⟩ := hcov u
    refine ⟨γ + u, hk, funext fun x => ?_⟩
    change chart φ.1 (unip u * G) _ = chart φ.1 (unip (γ + u) * G) _
    rw [chart_unip_add hφ.left G hγ u]
  have hs : ∀ u, ContDiffOn ℝ ∞ (H u) (invSet E (a - r)) := fun u =>
    (φ.2 (unip u * G)).comp (contDiff_blkA hr κ).contDiffOn fun x hx => blkA_mem hr κ hx
  have hm : ∀ m : ℕ, ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E (a - r) =>
      iteratedFDeriv ℝ m (H p.1) p.2) (Set.univ ×ˢ invSet E (a - r)) := fun m p hp =>
    (continuousAt_iteratedFDeriv φ hφ.level hr κ G m p.1 hp.2).continuousWithinAt
  exact (contDiffOn_infty.2 fun n => contDiffOn_integral_param (μ.restrict 𝓕) isOpen_invSet hK n H hrep hs hm).congr
    fun x hx => chart_slice μ 𝓕 hr φ.1 m₁ t κ g hx

end GlobalTheory.SliceTwoSmooth
