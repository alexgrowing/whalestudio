import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopologyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ConvDeriv

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem deriv_eq_zero {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) {ψ ψ' : G → ℂ}
    (hd : ∀ y, HasDerivAt (fun t => ψ ((c t)⁻¹ * y)) (ψ' y) 0) {y : G} (hy : y ∉ tsupport ψ) : ψ' y = 0 := by
  have hev : (fun t => ψ ((c t)⁻¹ * y)) =ᶠ[nhds 0] fun _ => (0 : ℂ) := by
    have ht : Filter.Tendsto (fun t => (c t)⁻¹ * y) (nhds 0) (nhds y) := by
      have h1 : Continuous fun t => (c t)⁻¹ * y := hc.inv.mul continuous_const
      simpa [h0] using h1.tendsto 0
    filter_upwards [ht ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hy)] with t ht'
    exact image_eq_zero_of_notMem_tsupport ht'
  exact (hd y).unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hev)

theorem hasDerivAt_shift {c : ℝ → G} (ha : ∀ a b, c (a + b) = c a * c b) {ψ ψ' : G → ℂ}
    (hd : ∀ y, HasDerivAt (fun t => ψ ((c t)⁻¹ * y)) (ψ' y) 0) (y : G) (s : ℝ) :
    HasDerivAt (fun t => ψ ((c t)⁻¹ * y)) (ψ' ((c s)⁻¹ * y)) s := by
  have h0' : HasDerivAt (fun t => ψ ((c t)⁻¹ * ((c s)⁻¹ * y))) (ψ' ((c s)⁻¹ * y)) (s - s) := by
    rw [sub_self]
    exact hd _
  have hfun : (fun t => ψ ((c t)⁻¹ * y)) = fun t => ψ ((c (t - s))⁻¹ * ((c s)⁻¹ * y)) := by
    funext t
    have e : c t = c s * c (t - s) := by
      rw [← ha]
      congr 1
      ring
    rw [e, _root_.mul_inv_rev, mul_assoc]
  rw [hfun]
  exact h0'.comp_sub_const s s

private lemma integrable_smul_of_bounded_compactSupport [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {φ : G → ℂ} {M : ℝ}
    (hφ : Continuous φ) (hM : ∀ z, ‖φ z‖ ≤ M) {K : Set G} (hK : IsCompact K) (hφK : ∀ z ∉ K, φ z = 0)
    {f : G → V} (hf : AEStronglyMeasurable f μ) (hfK : IntegrableOn f K μ) :
    Integrable (fun z => φ z • f z) μ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine Integrable.mono' (((integrable_indicator_iff hKm).2 hfK).norm.const_mul M)
    (hφ.aestronglyMeasurable.smul hf) (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz, norm_smul]
    exact mul_le_mul_of_nonneg_right (hM z) (norm_nonneg _)
  · rw [hφK z hz, _root_.zero_smul, norm_zero, Set.indicator_of_notMem hz, norm_zero, mul_zero]

theorem hasDerivAt_integral [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (ha : ∀ a b, c (a + b) = c a * c b) {ψ ψ' : G → ℂ}
    (hψ : Continuous ψ) (hψ' : Continuous ψ') (hs : HasCompactSupport ψ)
    (hd : ∀ y, HasDerivAt (fun t => ψ ((c t)⁻¹ * y)) (ψ' y) 0)
    {f : G → V} (hf : AEStronglyMeasurable f μ) (hi : ∀ K, IsCompact K → IntegrableOn f K μ) (x : G) :
    HasDerivAt (fun t => ∫ z, ψ ((x * c t)⁻¹ * z) • f z ∂μ) (∫ z, ψ' (x⁻¹ * z) • f z ∂μ) 0 := by
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hs
  have hz' : ∀ w, w ∉ tsupport ψ → ψ' w = 0 := fun w hw => deriv_eq_zero hc h0 hd hw
  obtain ⟨M', hM'⟩ := hψ'.bounded_above_of_compact_support (HasCompactSupport.intro hs.isCompact hz')
  obtain ⟨Kb, hKbc, hmem⟩ : ∃ Kb : Set G, IsCompact Kb ∧
      ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ z, (c t)⁻¹ * (x⁻¹ * z) ∈ tsupport ψ → z ∈ Kb := by
    refine ⟨(fun p : G × G => x * p.1 * p.2) '' ((c '' Metric.closedBall (0 : ℝ) 1) ×ˢ tsupport ψ),
      (((isCompact_closedBall 0 1).image hc).prod hs.isCompact).image
        ((continuous_const.mul continuous_fst).mul continuous_snd), ?_⟩
    intro t ht z hz
    exact ⟨(c t, (c t)⁻¹ * (x⁻¹ * z)), ⟨⟨t, Metric.ball_subset_closedBall ht, rfl⟩, hz⟩, by simp [mul_assoc]⟩
  have hfun : (fun t => ∫ z, ψ ((x * c t)⁻¹ * z) • f z ∂μ) =
      fun t => ∫ z, ψ ((c t)⁻¹ * (x⁻¹ * z)) • f z ∂μ := by
    funext t
    congr 1
    funext z
    rw [_root_.mul_inv_rev, mul_assoc]
  have hlim : (∫ z, ψ' (x⁻¹ * z) • f z ∂μ) = ∫ z, ψ' ((c 0)⁻¹ * (x⁻¹ * z)) • f z ∂μ := by
    simp [h0]
  rw [hfun, hlim]
  have hcz : ∀ t, Continuous fun z : G => (c t)⁻¹ * (x⁻¹ * z) := fun t =>
    continuous_const.mul (continuous_const.mul continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => ψ ((c t)⁻¹ * (x⁻¹ * z)) • f z)
    (F' := fun t z => ψ' ((c t)⁻¹ * (x⁻¹ * z)) • f z)
    (bound := fun z => M' * ‖Kb.indicator f z‖) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t => (hψ.comp (hcz t)).aestronglyMeasurable.smul hf)
    ?_ ((hψ'.comp (hcz 0)).aestronglyMeasurable.smul hf) ?_ ?_ ?_).2
  · exact integrable_smul_of_bounded_compactSupport μ (hψ.comp (hcz 0)) (fun z => hM _) hKbc
      (fun z hz => by
        show ψ ((c 0)⁻¹ * (x⁻¹ * z)) = 0
        exact image_eq_zero_of_notMem_tsupport fun h => hz (hmem 0 (Metric.mem_ball_self one_pos) z h))
      hf (hi _ hKbc)
  · refine Filter.Eventually.of_forall fun z t ht => ?_
    show ‖ψ' ((c t)⁻¹ * (x⁻¹ * z)) • f z‖ ≤ M' * ‖Kb.indicator f z‖
    by_cases hw : (c t)⁻¹ * (x⁻¹ * z) ∈ tsupport ψ
    · rw [Set.indicator_of_mem (hmem t ht z hw), norm_smul]
      exact mul_le_mul_of_nonneg_right (hM' _) (norm_nonneg _)
    · rw [hz' _ hw, _root_.zero_smul, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hM' 1)) (norm_nonneg _)
  · exact ((integrable_indicator_iff hKbc.isClosed.measurableSet).2 (hi _ hKbc)).norm.const_mul M'
  · exact Filter.Eventually.of_forall fun z t _ => (hasDerivAt_shift ha hd (x⁻¹ * z) t).smul_const (f z)

end General

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  have h := uMat_expU (0 : gLie ε)
  rw [ZeroMemClass.coe_zero, NormedSpace.exp_zero] at h
  exact Subtype.ext (Units.ext h)

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  show uMat (expU ((a + b) • X)) = uMat (expU (a • X)) * uMat (expU (b • X))
  rw [uMat_expU, uMat_expU, uMat_expU, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, _root_.add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU (t • (-X)) := by
  have h := expU_add X t (-t)
  rw [_root_.add_neg_cancel, _root_.zero_smul, expU_zero] at h
  rw [_root_.smul_neg, ← _root_.neg_smul]
  exact inv_eq_of_mul_eq_one_right h.symm

theorem hasDerivAt_exp_mul {n : ℕ} (Y M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • Y) * M) i j) ((Y * M) i j) 0 := by
  open Matrix.Norms.Operator in
  · have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y) * M)
        (NormedSpace.exp ((0 : ℝ) • Y) * Y * M) 0 :=
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)).mul_const M
    rw [_root_.zero_smul, NormedSpace.exp_zero, one_mul] at h1
    let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  have hexp : ∀ Y : gLie ε, Continuous fun t : ℝ =>
      ((expU (t • Y) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    intro Y
    have h : (fun t : ℝ => ((expU (t • Y) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun t => NormedSpace.exp (t • (Y : Matrix (Fin n) (Fin n) ℂ)) := by
      funext t
      rw [← Submodule.coe_smul, ← uMat_expU]
    rw [h]
    open Matrix.Norms.Operator in
    · exact continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) t).continuousAt
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hexp X, ?_⟩)
  convert hexp (-X) using 1
  funext t
  rw [← expU_inv]
  rfl

private lemma uMat_expU_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) =
      NormedSpace.exp (t • ((-X : gLie ε) : Matrix (Fin n) (Fin n) ℂ)) * uMat g := by
  rw [expU_inv, ← Submodule.coe_smul, ← uMat_expU]
  rfl

theorem convolution_hasDerivAt : ∀ (B : RowsAut) (A : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (χ : B.I.Gf → ℂ) (ψ : B.I.GA → ℂ) (E : gInf B), ContDiff ℝ ∞ A → HasCompactSupport A → Continuous χ → HasCompactSupport χ → (∀ y, ψ y = A (fun v i j => uMat (y.1 v) i j) * χ y.2) → Continuous ψ ∧ HasCompactSupport ψ ∧ ∃ ψ' : B.I.GA → ℂ, Continuous ψ' ∧ HasCompactSupport ψ' ∧ ∀ F : B.I.L2 B.μf B.fund, HasDerivAt (fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf))) (∫ y, ψ' y • B.R y F ∂(B.I.muA B.μf)) 0 ∧ ∀ x : B.I.GA, HasDerivAt (fun t : ℝ => ∫ z, ψ ((x * ((fun v => expU (t • E v)), 1))⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) (∫ z, ψ' (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) 0 := by
  intro B A χ ψ E hA hAs hχ hχs hψ
  obtain ⟨hT2f, -, hSCf, -⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology B.I
  haveI := hT2f
  haveI := hSCf
  haveI : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  obtain ⟨-, hRmul, -, hRc, hRext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  haveI : (B.I.muA B.μf).IsMulLeftInvariant := ⟨fun g => (GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf).1 g⟩
  have hu : ∀ v, Continuous fun y : B.I.GA => uMat (y.1 v) := fun v =>
    (Units.continuous_val.comp continuous_subtype_val).comp ((continuous_apply v).comp continuous_fst)
  let m : B.I.GA → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) := fun y v i j => uMat (y.1 v) i j
  let D : B.I.GA → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) := fun y v i j =>
    ((((-(E v)) : gLie (B.I.ε v)) : Matrix (Fin B.I.n) (Fin B.I.n) ℂ) * uMat (y.1 v)) i j
  let ψ' : B.I.GA → ℂ := fun y => fderiv ℝ A (m y) (D y) * χ y.2
  let c : ℝ → B.I.GA := fun t => ((fun v => expU (t • E v)), 1)
  have hm : Continuous m :=
    continuous_pi fun v => continuous_pi fun i => continuous_pi fun j => (hu v).matrix_elem i j
  have hD : Continuous D :=
    continuous_pi fun v => continuous_pi fun i => continuous_pi fun j =>
      (continuous_const.matrix_mul (hu v)).matrix_elem i j
  obtain ⟨K1, hK1c, hK1⟩ : ∃ K1 : Set B.I.Ginf, IsCompact K1 ∧
      ∀ g : B.I.Ginf, (fun v i j => uMat (g v) i j :
        InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) ∈ tsupport A → g ∈ K1 := by
    refine ⟨Set.pi Set.univ fun v => (fun g : Formalism.REAL.UJ (B.I.ε v) => uMat g) ⁻¹'
        ((fun p => p v) '' tsupport A),
      isCompact_univ_pi fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1.isCompact_preimage
        (hAs.isCompact.image (continuous_apply v)), ?_⟩
    intro g hg v _
    exact ⟨_, hg, rfl⟩
  have hsplit : ∀ y : B.I.GA, y ∉ K1 ×ˢ tsupport χ → m y ∉ tsupport A ∨ χ y.2 = 0 := by
    intro y hy
    rw [Set.mem_prod, not_and_or] at hy
    rcases hy with h | h
    · exact Or.inl fun h' => h (hK1 _ h')
    · exact Or.inr (image_eq_zero_of_notMem_tsupport h)
  have hψc : Continuous ψ := by
    rw [show ψ = fun y => A (m y) * χ y.2 from funext hψ]
    exact (hA.continuous.comp hm).mul (hχ.comp continuous_snd)
  have hψs : HasCompactSupport ψ := HasCompactSupport.intro (hK1c.prod hχs.isCompact) fun y hy => by
    rw [hψ]
    rcases hsplit y hy with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
    · rw [h, mul_zero]
  have hψ'c : Continuous ψ' :=
    (((hA.continuous_fderiv (by simp)).comp hm).clm_apply hD).mul (hχ.comp continuous_snd)
  have hψ's : HasCompactSupport ψ' := HasCompactSupport.intro (hK1c.prod hχs.isCompact) fun y hy => by
    show fderiv ℝ A (m y) (D y) * χ y.2 = 0
    rcases hsplit y hy with h | h
    · have h0 : fderiv ℝ A (m y) = 0 :=
        Function.notMem_support.1 fun h' => h (support_fderiv_subset ℝ h')
      rw [h0, ContinuousLinearMap.zero_apply, zero_mul]
    · rw [h, mul_zero]
  have hcc : Continuous c := (continuous_pi fun v => continuous_expU (E v)).prodMk continuous_const
  have hc0 : c 0 = 1 := by
    refine Prod.ext (funext fun v => ?_) rfl
    show expU ((0 : ℝ) • E v) = 1
    rw [_root_.zero_smul]
    exact expU_zero
  have hcadd : ∀ a b : ℝ, c (a + b) = c a * c b := fun a b =>
    Prod.ext (funext fun v => expU_add (E v) a b) (mul_one 1).symm
  have hd : ∀ y : B.I.GA, HasDerivAt (fun t => ψ ((c t)⁻¹ * y)) (ψ' y) 0 := by
    intro y
    let P : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) := fun t v i j =>
      (NormedSpace.exp (t • (((-(E v)) : gLie (B.I.ε v)) : Matrix (Fin B.I.n) (Fin B.I.n) ℂ)) *
        uMat (y.1 v)) i j
    have hP : HasDerivAt P (D y) 0 := by
      rw [hasDerivAt_pi]
      intro v
      rw [hasDerivAt_pi]
      intro i
      rw [hasDerivAt_pi]
      intro j
      exact hasDerivAt_exp_mul _ _ i j
    have hP0 : P 0 = m y := by
      funext v i j
      simp only [P, m, _root_.zero_smul, NormedSpace.exp_zero, one_mul]
    have key : HasDerivAt (fun t => A (P t) * χ y.2) (ψ' y) 0 := by
      have h1 := ((hA.differentiable (by simp)) (P 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hP
      rw [hP0] at h1
      exact h1.mul_const (χ y.2)
    have e : (fun t : ℝ => ψ ((c t)⁻¹ * y)) = fun t => A (P t) * χ y.2 := by
      funext t
      rw [hψ]
      refine congrArg₂ (· * ·) (congrArg A ?_) (congrArg χ ?_)
      · funext v i j
        exact congrFun (congrFun (uMat_expU_inv_mul (E v) t (y.1 v)) i) j
      · show (1 : B.I.Gf)⁻¹ * y.2 = y.2
        rw [_root_.inv_one, one_mul]
    rw [e]
    exact key
  refine ⟨hψc, hψs, ψ', hψ'c, hψ's, fun F => ⟨?_, fun x => ?_⟩⟩
  · have hint : Integrable (fun y => ψ y • B.R y F) (B.I.muA B.μf) :=
      (hψc.smul (hRc F)).integrable_of_hasCompactSupport hψs.smul_right
    have heq : (fun t => B.R (c t) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf))) =
        fun t => ∫ z, ψ ((1 * c t)⁻¹ * z) • B.R z F ∂(B.I.muA B.μf) := by
      funext t
      rw [← ContinuousLinearMap.integral_comp_comm _ hint]
      refine (integral_congr_ae ?_).trans
        (integral_mul_left_eq_self (fun z => ψ ((1 * c t)⁻¹ * z) • B.R z F) (c t))
      refine Filter.Eventually.of_forall fun y => ?_
      show B.R (c t) (ψ y • B.R y F) = ψ ((1 * c t)⁻¹ * (c t * y)) • B.R (c t * y) F
      rw [map_smul, one_mul, _root_.inv_mul_cancel_left, hRmul]
      rfl
    show HasDerivAt (fun t => B.R (c t) (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf)))
      (∫ y, ψ' y • B.R y F ∂(B.I.muA B.μf)) 0
    rw [heq]
    have h := hasDerivAt_integral (B.I.muA B.μf) hcc hc0 hcadd hψc hψ'c hψs hd
      (f := fun z => B.R z F) (hRc F).aestronglyMeasurable
      (fun K hK => (hRc F).continuousOn.integrableOn_compact hK) 1
    simpa only [_root_.inv_one, one_mul] using h
  · have h := hasDerivAt_integral (B.I.muA B.μf) hcc hc0 hcadd hψc hψ'c hψs hd
      (f := B.I.ext F) (hRext F).2
      (fun K hK => by
        obtain ⟨M, hM⟩ := GlobalTheory.LocalL2Isometry.ext_integrableOn B K hK
        exact (hM F).1) x
    show HasDerivAt (fun t => ∫ z, ψ ((x * c t)⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf))
      (∫ z, ψ' (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) 0
    simpa only [smul_eq_mul] using h

end GlobalTheory.ConvDeriv
