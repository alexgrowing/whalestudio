import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyOnto
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedKFiniteFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding

noncomputable section

open MeasureTheory Matrix Topology Set Filter GlobalTheory.Doubling GlobalTheory.EisCont
open CompanionTheory.D.gk.admitted.Gard (contDiff_integral_comp contDiff_Phi isCompact_mul_inv integral_mul_right_of_conj)
open scoped ContDiff NNReal

namespace GlobalTheory.EisCont.Smooth

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem isOpenEmbedding_val (N : ℕ) : IsOpenEmbedding (Units.val : GL (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
  haveI : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  (j : H →* G) (ι : H →* Matrix (Fin N) (Fin N) ℂ)

def MatSmooth (φ : G → ℂ) : Prop :=
  ∀ (C : Set G) [CompactSpace C], ∃ Φ : Matrix (Fin N) (Fin N) ℂ → C(C, ℂ), ContDiff ℝ ∞ Φ ∧
    ∀ (c : C) (x : H), φ (c * j x) = Φ (ι x) c

variable {j ι} {φ : G → ℂ}

omit [IsTopologicalGroup G] in
theorem MatSmooth.continuous [LocallyCompactSpace G] (h : MatSmooth j ι φ) : Continuous φ := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
  haveI := isCompact_iff_compactSpace.1 hC
  obtain ⟨Φ, -, e⟩ := h C
  refine ContinuousOn.continuousAt (continuousOn_iff_continuous_restrict.2 ?_) hg
  convert (Φ (ι 1)).continuous using 1
  funext c
  simpa using e c 1

omit [IsTopologicalGroup G] in
theorem MatSmooth.der (h : MatSmooth j ι φ) {x : ℝ → H} (hx : ContDiff ℝ ∞ fun t => ι (x t)) :
    MatSmooth j ι fun g => deriv (fun t => φ (g * j (x t))) 0 := by
  intro C _
  obtain ⟨Φ, hΦ, e⟩ := h C
  have hm : ∀ M : Matrix (Fin N) (Fin N) ℂ, ContDiff ℝ ∞ fun X : Matrix (Fin N) (Fin N) ℂ => X * M := fun M =>
    CompanionTheory.D.gk.admitted.Gard.contDiff_mul.comp (contDiff_id.prodMk contDiff_const)
  refine ⟨fun X => fderiv ℝ Φ (X * ι (x 0)) (X * deriv (fun t => ι (x t)) 0),
    ((hΦ.fderiv_right (m := ∞) le_rfl).comp (hm _)).clm_apply (hm _), fun c y => ?_⟩
  have h1 := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (ι y))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hx.differentiable (by simp) 0).hasDerivAt
  have h2 := (ContinuousMap.evalCLM (M := ℂ) ℝ c).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1)
  refine Eq.trans (congrArg (fun u : ℝ → ℂ => deriv u 0) (funext fun t => ?_)) h2.deriv
  rw [mul_assoc, ← map_mul, e, map_mul]
  rfl

omit [IsTopologicalGroup G] in
theorem MatSmooth.contDiff (h : MatSmooth j ι φ) {k : ℕ} {x : Fin k → ℝ → H} (hx : ∀ i, ContDiff ℝ ∞ fun t => ι (x i t))
    (g : G) : ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => j (x i (t i))).prod) := by
  obtain ⟨Φ, hΦ, e⟩ := h {g}
  have key : ∀ l : List (Fin k), ContDiff ℝ ∞ fun t : Fin k → ℝ => ι (l.map fun i => x i (t i)).prod := fun l => by
    induction l with
    | nil => exact contDiff_const (c := ι 1)
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      exact CompanionTheory.D.gk.admitted.Gard.contDiff_mul.comp (((hx i).comp (contDiff_apply ℝ ℝ i)).prodMk ih)
  have h2 := (ContinuousMap.evalCLM (M := ℂ) ℝ (⟨g, rfl⟩ : ({g} : Set G))).contDiff.comp (hΦ.comp (key (List.ofFn id)))
  convert h2 using 1
  funext t
  refine Eq.trans ?_ (e ⟨g, rfl⟩ _)
  simp [map_list_prod, List.map_ofFn, Function.comp_def]

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

theorem isCompact_preimage (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {T : Set (Matrix (Fin N) (Fin N) ℂ)}
    (hT : IsCompact T) : IsCompact (ι ⁻¹' T) := by
  have h2 : IsCompact (Units.val ⁻¹' (T ∩ {B | ‖B.det‖ = 1})) := (isOpenEmbedding_val N).isInducing.isCompact_preimage'
    (hT.inter_right (isClosed_eq continuous_id.matrix_det.norm continuous_const)) fun B hB =>
      (Matrix.isUnit_iff_isUnit_det B).2 (IsUnit.mk0 _ fun e => by simpa [e] using hB.2)
  convert (GlobalTheory.SmoothFactor.isClosedEmbedding_toHomUnits (ι := ι) hι).isCompact_preimage h2 using 1
  exact Set.ext fun y => (and_iff_left (h1 y)).symm

structure IsBump (f : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  nonneg : 0 ≤ f
  one : f 1 ≠ 0
  supp : ∃ S, IsCompact S ∧ (∀ B ∈ S, B.det ≠ 0) ∧ ∀ y, f y ≠ 0 → y ∈ S
  conj : ∀ k ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ y, f (kᴴ * y * k) = f y

variable {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

theorem IsBump.supp_local (hf : IsBump f) (X₀ : Matrix (Fin N) (Fin N) ℂ) :
    ∃ U ∈ 𝓝 X₀, ∃ C : Set H, IsCompact C ∧ ∀ X ∈ U, ∀ y ∉ C, f (ι y⁻¹ * X) = 0 := by
  obtain ⟨S, hS, hd, hfS⟩ := hf.supp
  refine ⟨Metric.closedBall X₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    isCompact_preimage hι h1 (isCompact_mul_inv (isCompact_closedBall X₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, ι x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have e : g = ι x * (ι x⁻¹ * g) := by rw [← Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mul]
  show g * (ι x⁻¹ * g)⁻¹ = ι x
  nth_rewrite 1 [e]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hd _ hB).isUnit, Matrix.mul_one]

theorem IsBump.weight (hf : IsBump f) (X : Matrix (Fin N) (Fin N) ℂ) :
    (Continuous fun y => f (ι y⁻¹ * X)) ∧ HasCompactSupport fun y => f (ι y⁻¹ * X) :=
  let ⟨_, hU, _, hC, h⟩ := hf.supp_local hι h1 X
  ⟨hf.smooth.continuous.comp ((hι.continuous.comp continuous_inv).mul continuous_const),
    .intro hC (h X (mem_of_mem_nhds hU))⟩

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

theorem exists_bump {V : Set (Matrix (Fin N) (Fin N) ℂ)} (hV : V ∈ 𝓝 1) :
    ∃ f, IsBump f ∧ (∀ X, f X ≠ 0 → X ∈ V) ∧ ∫ y, f (ι y⁻¹ * 1) ∂μ = 1 := by
  have hD : {y : Matrix (Fin N) (Fin N) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin N) (Fin N) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, h0, hf1, hS, hSW, hfS, hk⟩ := CompanionTheory.D.gk.admitted.Gard.exists_bump (inter_mem hV hD)
  have hb : IsBump f := ⟨hf, h0, hf1, ⟨S, hS, fun B hB => (hSW hB).2, hfS⟩, hk⟩
  obtain ⟨hw, hc⟩ := hb.weight hι h1 1
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := 1) hc (fun _ => h0 _) (by simpa using hf1)
  refine ⟨fun X => (∫ y, f (ι y⁻¹ * 1) ∂μ)⁻¹ * f X, ⟨contDiff_const.mul hf, fun X => mul_nonneg (inv_pos.2 hpos).le (h0 X),
    mul_ne_zero (inv_pos.2 hpos).ne' hf1, ⟨S, hS, fun B hB => (hSW hB).2, fun X h => hfS X (right_ne_zero_of_mul h)⟩,
    fun k h X => by rw [hk k h]⟩, fun X h => (hSW (hfS X (right_ne_zero_of_mul h))).1, ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

variable (j ι) in

def avg (f : Matrix (Fin N) (Fin N) ℂ → ℝ) (ψ : G → ℂ) : G → ℂ := fun g => ∫ y, f (ι y⁻¹ * 1) • ψ (g * j y) ∂μ

variable (hj : Continuous j) {ψ : G → ℂ}
include hj

theorem matSmooth_avg (hf : IsBump f) (hψ : Continuous ψ) : MatSmooth j ι (avg j ι μ f ψ) := by
  intro C _
  let v : C(H, C(C, ℂ)) := ContinuousMap.curry ⟨fun p : H × C => ψ (p.2 * j p.1), by fun_prop⟩
  have hq : Continuous fun y => (ι y⁻¹, v y) := (hι.continuous.comp continuous_inv).prodMk v.continuous
  have key := contDiff_integral_comp μ _ (contDiff_Phi (H := C(C, ℂ)) hf.smooth) _ hq fun X₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := hf.supp_local hι h1 X₀
    exact ⟨U, hU, C, hC, fun X hX y hy => by simp only [h X hX y hy, zero_smul]⟩
  refine ⟨_, key, fun c x => ?_⟩
  obtain ⟨hw, hc⟩ := hf.weight hι h1 (ι x)
  refine Eq.trans ?_ ((ContinuousMap.evalCLM (M := ℂ) ℝ c).integral_comp_comm
    ((hw.smul v.continuous).integrable_of_hasCompactSupport (μ := μ) hc.smul_right))
  rw [← integral_mul_left_eq_self _ x]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp [v, ← map_mul, mul_assoc]

theorem integrable_avg (hf : IsBump f) (hψ : Continuous ψ) (g : G) :
    Integrable (fun y => f (ι y⁻¹ * 1) • ψ (g * j y)) μ :=
  let ⟨hw, hc⟩ := hf.weight hι h1 1
  (hw.smul (by fun_prop)).integrable_of_hasCompactSupport hc.smul_right

omit [TopologicalSpace G] [IsTopologicalGroup G] hj in
theorem avg_mul (hf : IsBump f) {k : G} {κ : H} (hκ : ι κ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hk : ∀ y, k * j y = j (κ * y * κ⁻¹) * k) (g : G) : avg j ι μ f ψ (g * k) = avg j ι μ f (fun x => ψ (x * k)) g := by
  obtain ⟨hw, hc⟩ := hf.weight hι h1 1
  have e : (ι κ)ᴴ = ι κ⁻¹ :=
    (Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hκ)).symm.trans
      (Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one]))
  have e2 : ∀ y, f (ι (κ * y * κ⁻¹)⁻¹ * 1) = f (ι y⁻¹ * 1) := fun y => by
    rw [← hf.conj _ hκ, e]
    simp [← map_mul, mul_assoc]
  rw [avg, avg, ← integral_mul_right_of_conj μ hw hc (fun _ => hf.nonneg _) (by simpa using hf.one) κ⁻¹
    (by simpa only [inv_inv] using e2) fun y => f (ι y⁻¹ * 1) • ψ (g * j y * k),
    ← integral_mul_left_eq_self (fun y => f (ι (y * κ⁻¹)⁻¹ * 1) • ψ (g * j (y * κ⁻¹) * k)) κ]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [e2, mul_assoc g, hk]

theorem tendsto_avg {f : ℕ → Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : ∀ i, IsBump (f i))
    (hs : ∀ i X, f i X ≠ 0 → X ∈ Metric.ball 1 (1 / (i + 1 : ℝ))) (hm : ∀ i, ∫ y, f i (ι y⁻¹ * 1) ∂μ = 1)
    (hψ : Continuous ψ) (g : G) : Tendsto (fun i => avg j ι μ (f i) ψ g) atTop (𝓝 (ψ g)) := by
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε hε => ?_
  have hV : {y : H | ‖ψ (g * j y⁻¹) - ψ g‖ < ε} ∈ 𝓝 1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hε)
  rw [hι.isInducing.nhds_eq_comap, map_one, mem_comap] at hV
  obtain ⟨U, hU, hUV⟩ := hV
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)] with i hi
  obtain ⟨hw, hc⟩ := (hf i).weight hι h1 1
  have hI : Integrable (fun y => f i (ι y⁻¹ * 1)) μ := hw.integrable_of_hasCompactSupport hc
  have e : avg j ι μ (f i) ψ g - ψ g = ∫ y, f i (ι y⁻¹ * 1) • (ψ (g * j y) - ψ g) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub (integrable_avg hι h1 μ hj (hf i) hψ g) (hI.smul_const _), integral_smul_const, hm, one_smul, avg]
  rw [mem_closedBall_iff_norm, e]
  refine (norm_integral_le_of_norm_le (hI.mul_const ε) (.of_forall fun y => ?_)).trans
    (by rw [integral_mul_const, hm, one_mul])
  rw [norm_smul, Real.norm_of_nonneg ((hf i).nonneg _)]
  by_cases hy : f i (ι y⁻¹ * 1) = 0
  · simp only [hy, zero_mul, le_rfl]
  · have := hUV (a := y⁻¹) (hrU (Metric.ball_subset_ball hi.le (by simpa only [mul_one] using hs i _ hy)))
    exact mul_le_mul_of_nonneg_left (by simpa only [mem_setOf_eq, inv_inv] using le_of_lt (mem_setOf.1 this)) ((hf i).nonneg _)

include μ in

theorem matSmooth_of_mem [LocallyCompactSpace G] {P K : Subgroup G} {δ : P →* ℝ≥0} {χ : P →* Circle} {t : ℂ}
    (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k)
    (hK : ∀ k ∈ K, ∃ κ, ι κ ∈ Matrix.unitaryGroup (Fin N) ℂ ∧ ∀ y, k * j y = j (κ * y * κ⁻¹) * k)
    (hφ : φ ∈ indSpace δ K χ t) : MatSmooth j ι φ := by
  let W : Submodule ℂ (G → ℂ) :=
    { carrier := {ψ | ψ ∈ domSet δ K χ t φ ∧ Continuous ψ}
      zero_mem' := ⟨⟨fun _ _ => by simp, fun _ _ _ => by simp⟩, continuous_zero⟩
      add_mem' := fun h h' => ⟨⟨fun p g => by simp only [Pi.add_apply, h.1.1 p g, h'.1.1 p g, mul_add], fun c hc g => by
        simpa only [Finsupp.sum, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_zero] using
          congrArg₂ (· + ·) (h.1.2 c hc g) (h'.1.2 c hc g)⟩, h.2.add h'.2⟩
      smul_mem' := fun a ψ h => ⟨⟨fun p g => by simp only [Pi.smul_apply, h.1.1 p g, smul_eq_mul]; ring, fun c hc g => by
        simpa only [Finsupp.sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm a, mul_zero] using
          congrArg (a * ·) (h.1.2 c hc g)⟩, h.2.const_smul a⟩ }
  haveI := GlobalTheory.EisCont.finiteDimensional_span_domSet G P K δ χ t φ hI hφ.2.2
  haveI : FiniteDimensional ℂ W :=
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (domSet δ K χ t φ)) fun ψ h => Submodule.subset_span h.1
  choose f hf hs hm using fun i : ℕ => exists_bump hι h1 μ (Metric.ball_mem_nhds 1 (Nat.one_div_pos_of_nat (n := i)))
  have hW : ∀ i, ∀ ψ ∈ W, avg j ι μ (f i) ψ ∈ W := fun i ψ h => by
    refine ⟨⟨fun p g => ?_, fun c hc g => ?_⟩, (matSmooth_avg hι h1 μ hj (hf i) h.2).continuous⟩
    · simp only [avg, mul_assoc (p : G), h.1.1 p, ← integral_const_mul, mul_smul_comm]
    · choose κ h2 h3 using hK
      simp only [Finsupp.sum, fun k : K => avg_mul hι h1 μ (ψ := ψ) (hf i) (h2 _ k.2) (h3 _ k.2) g]
      simp only [avg, ← integral_const_mul]
      rw [← integral_finsetSum _ fun (k : K) _ =>
        (integrable_avg hι h1 μ hj (hf i) (ψ := fun x => ψ (x * k)) (h.2.comp (by fun_prop)) g).const_mul _]
      refine (integral_congr_ae (.of_forall fun y => ?_)).trans (integral_zero _ _)
      simpa only [Finsupp.sum, Finset.smul_sum, mul_smul_comm, smul_zero] using
        congrArg (f i (ι y⁻¹ * 1) • ·) (h.1.2 c hc (g * j y))
  let T : ℕ → W →ₗ[ℂ] W := fun i =>
    { toFun := fun ψ => ⟨_, hW i ψ.1 ψ.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by
        simpa only [avg, Submodule.coe_add, Pi.add_apply, smul_add] using
          integral_add (integrable_avg hι h1 μ hj (hf i) a.2.2 g) (integrable_avg hι h1 μ hj (hf i) b.2.2 g))
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        simp only [avg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, ← integral_smul, smul_comm c]) }
  obtain ⟨i, hi⟩ := GlobalTheory.ApproxOnto.eventually_onto G W T fun ψ g => tendsto_avg hι h1 μ hj hf hs hm ψ.2.2 g
  obtain ⟨ψ, e⟩ := hi ⟨φ, ⟨hφ.1, .refl K φ⟩, hφ.2.1⟩
  exact (show avg j ι μ (f i) ψ = φ from congrArg Subtype.val e) ▸ matSmooth_avg hι h1 μ hj (hf i) ψ.2.2

end Abstract

section Unitary

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem norm_det_archMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w)
    (x : GArch σ J w) : ‖(archMat σ J τ x).det‖ = 1 := by
  have hu : (archMat σ J τ x)ᴴ * J.map τ.1 * archMat σ J τ x = J.map τ.1 := (archEquiv J h τ x).2
  have hd : ‖(J.map τ.1).det‖ ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hJ.2
  have := congrArg (fun X => ‖X.det‖) hu
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star] at this
  rw [mul_right_comm, mul_eq_right₀ hd] at this
  nlinarith [norm_nonneg (archMat σ J τ x).det]

attribute [-instance] Matrix.normedAddCommGroup Matrix.normedSpace in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem contDiff_exp_entry (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => NormedSpace.exp (t • Z) a b := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h1 : ContDiff ℝ ∞ fun t : ℝ => NormedSpace.exp (t • Z) :=
    (contDiff_iff_contDiffAt.2 fun X => (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt).comp (contDiff_id.smul contDiff_const)
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp h1

theorem exists_mat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)) :
    ∃ (N : ℕ) (ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ), IsEmbedding ι ∧ (∀ y, ‖(ι y).det‖ = 1) ∧
      (∀ κ, (∀ w, projInfArch σ J w κ ∈ stabArch σ J w (c w)) → ι κ ∈ Matrix.unitaryGroup (Fin N) ℂ) ∧
      ∀ γ, IsRealLine σ J γ → ∃ x : ℝ → GInf σ J, (∀ t, γ t = ofInf σ J (x t)) ∧ ContDiff ℝ ∞ fun t => ι (x t) := by
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun _ => Classical.arbitrary _
  let b : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) →* Matrix (Fin n) (Fin n) ℂ := fun w =>
    (infEmb (τ w)).mapMatrix.toMonoidHom.comp (Units.coeHom _)
  let u : ∀ w : InfinitePlace F, GInf σ J →* Matrix (Fin n) (Fin n) ℂ := fun w =>
    (b w).comp ((MulAut.conj (c w)⁻¹).toMonoidHom.comp ((matHom _ σ J).comp (projInfArch σ J w)))
  have hu0 : ∀ w y, u w y = b w ((c w)⁻¹ * matHom _ σ J (projInfArch σ J w y) * c w) := fun w y => by simp [u]
  have hu : ∀ w y, u w y = b w (c w)⁻¹ * archMat σ J (τ w) (projInfArch σ J w y) * b w (c w) := fun w y => by
    rw [hu0, map_mul, map_mul]; rfl
  have hb : ∀ w, b w (c w) * b w (c w)⁻¹ = 1 := fun w => by rw [← map_mul, mul_inv_cancel, map_one]
  let e := Fintype.equivFin (Fin n × InfinitePlace F)
  let ι : GInf σ J →* Matrix _ _ ℂ := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv.toMonoidHom.comp
    ((Matrix.blockDiagonalRingHom (Fin n) _ ℂ).toMonoidHom.comp (MonoidHom.pi u))
  have hι : ∀ y, ι y = (blockDiagonal fun w => u w y).submatrix e.symm e.symm := fun _ => rfl
  refine ⟨_, ι, ?_, fun y => ?_, fun κ hκ => ?_, ?_⟩
  · have h1 : IsEmbedding fun (g : GInf σ J) w => archMat σ J (τ w) (projInfArch σ J w g) :=
      (Topology.IsEmbedding.piMap fun w => isEmbedding_archMat J h (τ w)).comp
      (infContEquivPi σ J).toHomeomorph.isEmbedding
    have h2 : Continuous ι := by
      simp only [funext hι, hu]
      exact (Continuous.matrix_blockDiagonal (continuous_pi fun w => (continuous_const.matrix_mul
        ((continuous_archMat σ J _).comp (continuous_projInfArch σ J w))).matrix_mul continuous_const)).matrix_submatrix _ _
    refine Topology.IsEmbedding.of_comp (g := fun (y : Matrix _ _ ℂ) w =>
      b w (c w) * (Matrix.of fun i j => y (e (i, w)) (e (j, w))) * b w (c w)⁻¹) h2 (continuous_pi fun w =>
        (continuous_const.matrix_mul (continuous_matrix fun i j => by simp only [of_apply]; fun_prop)).matrix_mul
          continuous_const) ?_
    convert h1 using 1
    funext g w
    have : (Matrix.of fun i j => ι g (e (i, w)) (e (j, w))) = u w g := by
      ext i j; simp [hι]
    simp only [Function.comp_apply, this, hu, Matrix.mul_assoc, hb, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hb, Matrix.one_mul]
  · rw [hι, det_submatrix_equiv_self, det_blockDiagonal, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [hu, det_mul_comm, ← Matrix.mul_assoc, hb, Matrix.one_mul, norm_det_archMat h hJ]
  · have h1 : ∀ w, (u w κ)ᴴ * u w κ = 1 := fun w => by
      have h2 := mem_stabArch.1 (hκ w)
      rw [hu0]
      generalize (c w)⁻¹ * matHom _ σ J (projInfArch σ J w κ) * c w = x at h2 ⊢
      have h3 := congrArg (Matrix.map · (infEmb (τ w))) (show Formalism.UG.cT _ x.1 * 1 * x.1 = 1 from h2)
      simp only [mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Matrix.map_one _ (map_zero _) (map_one _)] at h3
      exact h3
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, hι, conjTranspose_submatrix, submatrix_mul_equiv,
      blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [h1]
    rw [show (fun _ => 1 : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) = 1 from rfl, blockDiagonal_one, submatrix_one_equiv]
  · rintro γ ⟨w, τ', Z, -, hγ⟩
    choose y e1 e2 using hγ
    refine ⟨fun t => embArchInf σ J w (y t), e1, ?_⟩
    have h1 : ∀ v p q, ContDiff ℝ ∞ fun t => archMat σ J (τ v) (projInfArch σ J v (embArchInf σ J w (y t))) p q := by
      intro v p q
      by_cases hv : v = w
      · subst hv
        simp only [projInfArch_embArchInf_self]
        have h2 := contDiff_exp_entry Z p q
        simp only [← e2, archMat_apply, map_apply] at h2 ⊢
        rcases infEmb_eq_or_conj h τ' (τ v) with e3 | e3 <;> rw [e3]
        exacts [h2, Complex.conjCLE.contDiff.comp h2]
      · simp only [projInfArch_embArchInf_ne σ J hv]
        exact contDiff_const
    refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
    simp only [hι, submatrix_apply, blockDiagonal_apply]
    split_ifs
    · simp only [hu, Matrix.mul_apply]
      exact ContDiff.sum fun _ _ => (ContDiff.sum fun _ _ => contDiff_const.mul (h1 _ _ _)).mul contDiff_const
    · exact contDiff_const

theorem isSm_of_mem (h : IsCMExt F E σ) (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
    {P : Subgroup (GAd σ J)} {δ : P →* ℝ≥0} {χ : P →* Circle} {t : ℂ}
    (hI : ∀ g : GAd σ J, ∃ p : P, ∃ k ∈ levelAll σ J L a, g = p * k) {φ : GAd σ J → ℂ}
    (hφ : φ ∈ indSpace δ (levelAll σ J L a) χ t) :
    IsSm σ J φ ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  obtain ⟨N, ι, hι, h1, hu, hx⟩ := exists_mat h hJ fun w => Formalism.UG.bc (compInf F E w) a
  have key : MatSmooth (ofInf σ J) ι φ := matSmooth_of_mem hι h1 Measure.haar (continuous_ofInf σ J) hI (fun k hk =>
    ⟨projInf σ J k, hu _ fun w => by simpa using (mem_levelAll.1 hk).2 w, fun y =>
      ext_inf_fin σ J (by simp) (by simp)⟩) hφ
  refine ⟨fun k γ hγ g => ?_, fun l hl => MatSmooth.continuous (j := ofInf σ J) (ι := ι) ?_⟩
  · choose x e hx using fun i => hx _ (hγ i)
    simpa only [e] using key.contDiff hx g
  · induction l with
    | nil => exact key
    | cons γ l ih =>
      obtain ⟨x, e, hx⟩ := hx γ (hl γ List.mem_cons_self)
      obtain rfl : γ = _ := funext e
      exact (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)).der hx

end Unitary

end GlobalTheory.EisCont.Smooth

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel
  GlobalTheory.RegSW GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
