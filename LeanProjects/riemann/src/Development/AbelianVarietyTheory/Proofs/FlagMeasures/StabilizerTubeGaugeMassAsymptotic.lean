import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PhiDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarDec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI.RhsWLim PI.RhsWLim.W

namespace GlobalTheory.StabTube

variable {k r : ℕ}

theorem tube_identity (G K : Set (Mat k r)) (μ ν : Measure (Mt k r)) [SFinite μ] [SFinite ν]
    (hμ : μ {x | Matrix.of x ∉ G} = 0) (hν : ν {x | Matrix.of x ∉ K} = 0)
    (hR : ∀ p ∈ K, μ.map (rmulM p) = μ) (hL : ∀ s ∈ K, ν.map (lmulM s) = ν)
    {T B S : Set (Mt k r)} (hT : MeasurableSet T) (hB : MeasurableSet B) (hS : MeasurableSet S)
    (h1 : ∀ g : Mt k r, Matrix.of g ∈ G → g ∈ T → ∃ h0 ∈ K, ∀ h : Mt k r, Matrix.of h ∈ K →
      (lmulM (Matrix.of g) h ∈ B ↔ lmulM h0 h ∈ S))
    (h2 : ∀ g : Mt k r, Matrix.of g ∈ G → g ∉ T → ∀ h : Mt k r, Matrix.of h ∈ K → lmulM (Matrix.of g) h ∉ B) :
    ν Set.univ * μ B = ν S * μ T := by
  have hc : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 :=
    Continuous.matrix_mul (A := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r))
      (B := fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) continuous_fst continuous_snd
  have hD : MeasurableSet ((fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) ⁻¹' B) := hc.measurable hB
  have e1 := Measure.prod_apply (μ := μ) (ν := ν) hD
  have e2 := Measure.prod_apply_symm (μ := μ) (ν := ν) hD
  have aμ : ∀ᵐ g ∂μ, Matrix.of g ∈ G := hμ
  have aν : ∀ᵐ h ∂ν, Matrix.of h ∈ K := hν
  rw [← lintegral_indicator_const hT, mul_comm, ← lintegral_const]
  refine Eq.trans (lintegral_congr_ae ?_) ((e2.symm.trans e1).trans (lintegral_congr_ae ?_))
  · filter_upwards [aν] with h hh
    have hm : Measurable (rmulM (Matrix.of h) : Mt k r → Mt k r) :=
      (hc.comp (continuous_id.prodMk continuous_const)).measurable
    conv_lhs => rw [← hR _ hh, Measure.map_apply hm hB]
    rfl
  · filter_upwards [aμ] with g hg
    by_cases hgT : g ∈ T
    · obtain ⟨h0, hh0, H⟩ := h1 g hg hgT
      rw [Set.indicator_of_mem hgT]
      conv_rhs => rw [← hL _ hh0, Measure.map_apply (HU.lmulM_cont h0).measurable hS]
      refine measure_congr ?_
      filter_upwards [aν] with h hh
      exact propext (H h hh)
    · rw [Set.indicator_of_notMem hgT]
      refine measure_mono_null (fun h hh => ?_) hν
      exact fun hK => h2 g hg hgT h hK hh

abbrev pw (k r : ℕ) : Fin (2 * r + k + 1) := wI k r (Fin.last k)

abbrev Kw (k r : ℕ) : Set (Mat k r) := UWset k r (wLast k r)

theorem mem_Kw {g : Mat k r} : g ∈ Kw k r ↔ g ∈ UWb k r ∧ g *ᵥ wLast k r = wLast k r :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem isMatGroup_UWb : PI.IsMatGroup (UWb k r) :=
  ⟨HU.amb_closed, HU.uwb_one, fun _ ha _ hb => HU.uwb_mul ha hb,
    fun a ha => ⟨HU.uwb_inv ha, Matrix.mul_nonsing_inv a (HU.uwb_unit ha)⟩⟩

theorem isMatGroup_Kw : PI.IsMatGroup (Kw k r) := by
  refine ⟨?_, mem_Kw.2 ⟨HU.uwb_one, Matrix.one_mulVec _⟩, fun a ha b hb => ?_, fun a ha => ?_⟩
  · have : Kw k r = UWb k r ∩ {g | g *ᵥ wLast k r = wLast k r} := Set.ext fun _ => mem_Kw
    rw [this]
    exact isMatGroup_UWb.1.inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  · rw [mem_Kw] at *
    exact ⟨HU.uwb_mul ha.1 hb.1, by rw [← Matrix.mulVec_mulVec, hb.2, ha.2]⟩
  · rw [mem_Kw] at *
    have hu := HU.uwb_unit ha.1
    refine ⟨⟨HU.uwb_inv ha.1, ?_⟩, Matrix.mul_nonsing_inv a hu⟩
    conv_lhs => rw [← ha.2]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem mem_lieE_iff {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : x ∈ lieE S ↔ unrealify x ∈ lieOf S := by
  refine ⟨fun h => GlobalTheory.ClosedMatGroup.unrealify_mem_lieOf hS h, fun h => ?_⟩
  refine Submodule.subset_span ⟨unrealify x, h, ?_⟩
  ext ⟨i, j, b⟩
  cases b <;> rfl

theorem exp_mem {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {X : Matrix (Fin m) (Fin m) ℂ} (h : X ∈ lieOf S) :
    NormedSpace.exp X ∈ S := by
  simpa using h 1

theorem mem_lieOf_Kw (X : Mat k r) : X ∈ lieOf (Kw k r) ↔ X ∈ lieOf (UWb k r) ∧ ∀ i, X i (pw k r) = 0 := by
  rw [← GlobalTheory.CellLieAlg.exp_fix_iff X (pw k r)]
  exact ⟨fun h => ⟨fun t => (mem_Kw.1 (h t)).1, fun t => (mem_Kw.1 (h t)).2⟩,
    fun h t => mem_Kw.2 ⟨h.1 t, h.2 t⟩⟩

theorem mem_lieOf_UWb (X : Mat k r) : X ∈ lieOf (UWb k r) ↔
    (∀ i j, star (HU.sgn k r j * X (HU.tau k r j) i) + HU.sgn k r i * X (HU.tau k r i) j = 0) ∧
      ∀ i j, ¬ (MB.mid k r i ∧ MB.mid k r j) → X i j = 0 := by
  refine (GlobalTheory.CellLieAlg.mem_lieOf_UWb k r X).trans (and_congr_left fun _ => ?_)
  change Xᴴ * Hpk k r + Hpk k r * X = 0 ↔ _
  have e : Xᴴ * Hpk k r = (Hpk k r * X)ᴴ := by rw [conjTranspose_mul, MB.hpk_herm]
  rw [e, ← Matrix.ext_iff]
  simp only [Matrix.add_apply, conjTranspose_apply, HU.hpk_mul_apply, Matrix.zero_apply]

theorem tau_mid {i : Fin (2 * r + k + 1)} (hi : MB.mid k r i) : HU.tau k r i = i := by
  apply Fin.ext
  simp only [HU.tau]
  rw [if_neg (by have := hi.1; have := hi.2; omega)]

theorem tau_not_mid {i : Fin (2 * r + k + 1)} (hi : ¬ MB.mid k r i) : ¬ MB.mid k r (HU.tau k r i) := fun h => by
  have := tau_mid h
  rw [HU.tau_tau] at this
  exact hi (this ▸ h)

theorem sgn_pw : HU.sgn k r (pw k r) = -1 := by simp [HU.sgn, wI]

theorem mid_cases {i : Fin (2 * r + k + 1)} (hi : MB.mid k r i) :
    (∃ a : Fin k, i = wI k r a.castSucc) ∨ i = pw k r := by
  rw [← MB.wI_midx hi]
  rcases Fin.eq_castSucc_or_eq_last (MB.midx hi) with ⟨a, h⟩ | h
  · exact Or.inl ⟨a, by rw [h]⟩
  · exact Or.inr (by rw [h])

theorem wc_ne (a : Fin k) : wI k r a.castSucc ≠ pw k r := fun h => Fin.castSucc_ne_last a (MB.wI_inj h)

theorem sgn_wc (a : Fin k) : HU.sgn k r (wI k r a.castSucc) = 1 := by
  have := a.isLt
  exact if_neg (by simp only [wI, Fin.val_castSucc]; omega)

theorem gen_off (q : TrE k) {i j : Fin (2 * r + k + 1)} (hi : i ≠ pw k r) (hj : j ≠ pw k r) :
    opGen k r q i j = 0 := by
  have hi' : i.val ≠ r + k := fun h => hi (Fin.ext h)
  have hj' : j.val ≠ r + k := fun h => hj (Fin.ext h)
  simp [opGen, hi', hj']

theorem gen_out (q : TrE k) (i j : Fin (2 * r + k + 1)) (h : ¬ (MB.mid k r i ∧ MB.mid k r j)) :
    opGen k r q i j = 0 := by
  unfold opGen
  simp only [MB.mid] at h
  split_ifs <;> first | rfl | (exfalso; omega)

theorem gen_wc (q : TrE k) (a : Fin k) : opGen k r q (pw k r) (wI k r a.castSucc) = star (opBeta k q a) := by
  simp [opGen, wI, a.isLt]

theorem gen_mem (q : TrE k) : opGen k r q ∈ lieOf (UWb k r) := by
  refine (mem_lieOf_UWb _).2 ⟨fun i j => ?_, gen_out q⟩
  by_cases hi : MB.mid k r i
  · by_cases hj : MB.mid k r j
    · rw [tau_mid hi, tau_mid hj]
      rcases mid_cases hi with ⟨a, rfl⟩ | rfl <;> rcases mid_cases hj with ⟨b, rfl⟩ | rfl
      · simp [gen_off q (wc_ne _) (wc_ne _)]
      · simp [sgn_pw, sgn_wc, gen_wc, opGen_y]
      · simp [sgn_pw, sgn_wc, gen_wc, opGen_y]
      · simp [sgn_pw, opGen_c]
    · rw [gen_out q _ i fun h => tau_not_mid hj h.1, gen_out q _ j fun h => hj h.2]; simp
  · rw [gen_out q _ i fun h => hi h.2, gen_out q _ j fun h => tau_not_mid hi h.1]; simp

theorem row_zero {X : Mat k r} (hX : X ∈ lieOf (Kw k r)) (j : Fin (2 * r + k + 1)) : X (pw k r) j = 0 := by
  obtain ⟨h1, h2⟩ := (mem_lieOf_Kw X).1 hX
  have := ((mem_lieOf_UWb X).1 h1).1 (pw k r) j
  rw [h2, tau_mid (MB.mid_wI _), sgn_pw] at this
  simpa using this

theorem sum_mid (f : Fin (2 * r + k + 1) → ℝ) (hf : ∀ i, ¬ MB.mid k r i → f i = 0) :
    ∑ i, f i = ∑ a : Fin k, f (wI k r a.castSucc) + f (pw k r) := by
  rw [← Fin.sum_univ_castSucc (fun m => f (wI k r m))]
  exact (Fintype.sum_of_injective (wI k r) (fun _ _ => MB.wI_inj) _ _
    (fun i hi => hf i fun h => hi ⟨_, MB.wI_midx h⟩) fun _ => rfl).symm

def genE (k r : ℕ) : TrE k →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) where
  toFun q := WithLp.toLp 2 (realifyFun (opGen k r q))
  map_add' q q' := by
    have : opGen k r (q + q') = opGen k r q + opGen k r q' := (opGenLin k r).map_add q q'
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, this]
  map_smul' c q := by
    have : opGen k r (c • q) = c • opGen k r q := (opGenLin k r).map_smul c q
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, this]

theorem unrealify_genE (q : TrE k) : unrealify (genE k r q) = opGen k r q := rfl

theorem normSq_beta (q : TrE k) (a : Fin k) :
    Complex.normSq (opBeta k q a) = (q (some (a, true)) ^ 2 + q (some (a, false)) ^ 2) / 2 := by
  rw [opBeta, map_div₀, Complex.normSq_add_mul_I, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num), add_comm]

theorem norm_genE (q : TrE k) : ‖genE k r q‖ ^ 2 = ‖q‖ ^ 2 := by
  have e : ‖genE k r q‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (opGen k r q i j) := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [genE, realifyFun, Complex.normSq_apply]
    ring
  have h1 : ∀ a : Fin k, ∑ j, Complex.normSq (opGen k r q (wI k r a.castSucc) j) = Complex.normSq (opBeta k q a) := by
    intro a
    rw [Finset.sum_eq_single (pw k r) (fun j _ hj => by rw [gen_off q (wc_ne a) hj, map_zero]) (by simp), opGen_y]
  rw [e, sum_mid _ fun i hi => Finset.sum_eq_zero fun j _ => by rw [gen_out q i j fun h => hi h.1, map_zero],
    sum_mid (fun j => Complex.normSq (opGen k r q (pw k r) j)) fun j hj => by
      rw [gen_out q _ j fun h => hj h.2, map_zero],
    EuclideanSpace.norm_sq_eq, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [h1, gen_wc, opGen_c, Complex.star_def, Complex.normSq_conj, normSq_beta, Fintype.sum_bool,
    Real.norm_eq_abs, sq_abs, map_mul, Complex.normSq_I, Complex.normSq_ofReal, ← Finset.sum_div]
  ring

theorem inner_genE (q : TrE k) (A : lieE (Kw k r)) : inner ℝ (genE k r q) (A : EuclideanSpace ℝ _) = 0 := by
  have hA := (mem_lieE_iff isMatGroup_Kw _).1 A.2
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun ⟨i, j, b⟩ _ => ?_
  by_cases h : i = pw k r ∨ j = pw k r
  · have h0 : unrealify (A : EuclideanSpace ℝ _) i j = 0 := by
      rcases h with rfl | rfl
      · exact row_zero hA j
      · exact ((mem_lieOf_Kw _).1 hA).2 i
    have : (A : EuclideanSpace ℝ _) (i, j, b) = 0 := by
      cases b
      · exact congrArg Complex.re h0
      · exact congrArg Complex.im h0
    rw [this, inner_zero_right]
  · rw [not_or] at h
    have : genE k r q (i, j, b) = 0 := by
      cases b <;> simp [genE, realifyFun, gen_off q h.1 h.2]
    rw [this, inner_zero_left]

theorem genE_mem (q : TrE k) : genE k r q ∈ lieE (UWb k r) := (mem_lieE_iff isMatGroup_UWb _).2 (gen_mem q)

theorem lieK_le : lieE (Kw k r) ≤ lieE (UWb k r) := fun _ hx =>
  (mem_lieE_iff isMatGroup_UWb _).2 ((mem_lieOf_Kw _).1 ((mem_lieE_iff isMatGroup_Kw _).1 hx)).1

def tang (k r : ℕ) : TrE k × lieE (Kw k r) →ₗ[ℝ] lieE (UWb k r) :=
  ((genE k r).codRestrict _ genE_mem).coprod (Submodule.inclusion lieK_le)

theorem coe_tang (v : TrE k × lieE (Kw k r)) :
    (tang k r v : EuclideanSpace ℝ _) = genE k r v.1 + (v.2 : EuclideanSpace ℝ _) := rfl

theorem norm_tang (v : TrE k × lieE (Kw k r)) : ‖tang k r v‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
  rw [← Submodule.norm_coe, coe_tang, norm_add_sq_real, inner_genE, norm_genE, Submodule.norm_coe]
  ring

theorem unrealify_sub {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x - y) = unrealify x - unrealify y := by
  ext i j; apply Complex.ext <;> simp [unrealify]

theorem unrealify_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j; apply Complex.ext <;> simp [unrealify]

theorem tang_surjective : Function.Surjective (tang k r) := by
  intro Y
  obtain ⟨h1, h2⟩ := (mem_lieOf_UWb _).1 ((mem_lieE_iff isMatGroup_UWb _).1 Y.2)
  set M := unrealify (Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) with hM
  let q : TrE k := WithLp.toLp 2 fun o => match o with
    | none => (M (pw k r) (pw k r)).im
    | some (a, b) => Real.sqrt 2 * (if b then (M (wI k r a.castSucc) (pw k r)).im else (M (wI k r a.castSucc) (pw k r)).re)
  have hq : ∀ i, M i (pw k r) = opGen k r q i (pw k r) := by
    intro i
    by_cases hi : MB.mid k r i
    · rcases mid_cases hi with ⟨a, rfl⟩ | rfl
      · have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
        rw [opGen_y, opBeta, eq_div_iff hs]
        apply Complex.ext <;> simp [q, mul_comm]
      · have := congrArg Complex.re (h1 (pw k r) (pw k r))
        rw [tau_mid (MB.mid_wI _), sgn_pw] at this
        rw [opGen_c]
        apply Complex.ext
        · simp at this ⊢; linarith
        · simp [q]
    · rw [h2 i _ fun h => hi h.1, gen_out q i _ fun h => hi h.1]
  have hA : (Y : EuclideanSpace ℝ _) - genE k r q ∈ lieE (Kw k r) := by
    refine (mem_lieE_iff isMatGroup_Kw _).2 ((mem_lieOf_Kw _).2
      ⟨(mem_lieE_iff isMatGroup_UWb _).1 (Submodule.sub_mem _ Y.2 (genE_mem q)), fun i => ?_⟩)
    rw [unrealify_sub, unrealify_genE, Matrix.sub_apply, ← hM, hq, sub_self]
  exact ⟨(q, ⟨_, hA⟩), Subtype.ext (by rw [coe_tang]; exact add_sub_cancel _ _)⟩

theorem measurePreserving_of_norm {A B D : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] (f : A × B →ₗ[ℝ] D)
    (hf : ∀ v, ‖f v‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) (hs : Function.Surjective f) :
    Function.Injective f ∧ MeasurePreserving f (volume.prod volume) volume := by
  let J : WithLp 2 (A × B) →ₗᵢ[ℝ] D :=
    { toFun := fun p => f (p.fst, p.snd)
      map_add' := fun p q => by rw [← map_add]; rfl
      map_smul' := fun c p => by rw [← map_smul]; rfl
      norm_map' := fun p => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
        exact hf _ }
  have hJ : Function.Surjective J := fun Y => by
    obtain ⟨v, hv⟩ := hs Y
    exact ⟨WithLp.toLp 2 v, hv⟩
  exact ⟨fun v w h => WithLp.toLp_injective 2 (J.injective (a₁ := WithLp.toLp 2 v) (a₂ := WithLp.toLp 2 w) h),
    (LinearIsometryEquiv.ofSurjective _ hJ).measurePreserving.comp (WithLp.volume_preserving_toLp _ _)⟩

theorem measurePreserving_tang : MeasurePreserving (tang k r) (volume.prod volume) volume :=
  (measurePreserving_of_norm _ norm_tang tang_surjective).2

theorem tang_injective : Function.Injective (tang k r) :=
  (measurePreserving_of_norm _ norm_tang tang_surjective).1

def tangEquiv (k r : ℕ) : (TrE k × lieE (Kw k r)) ≃L[ℝ] lieE (UWb k r) :=
  (LinearEquiv.ofBijective _ ⟨tang_injective, tang_surjective⟩).toContinuousLinearEquiv

theorem volume_tang_ball (ρ : ℝ) : volume (tangEquiv k r '' Metric.ball 0 ρ) =
    volume (Metric.ball (0 : TrE k) ρ) * volume (Metric.ball (0 : lieE (Kw k r)) ρ) := by
  have ho : IsOpen (tangEquiv k r '' Metric.ball 0 ρ) := (tangEquiv k r).toHomeomorph.isOpenMap _ Metric.isOpen_ball
  have hp : tang k r ⁻¹' (tangEquiv k r '' Metric.ball 0 ρ) = Metric.ball 0 ρ :=
    Set.preimage_image_eq _ (tangEquiv k r).injective
  rw [← measurePreserving_tang.measure_preimage ho.measurableSet.nullMeasurableSet, hp, ← Measure.prod_prod,
    ball_prod_same]
  rfl

def chart (k r : ℕ) (v : TrE k × lieE (Kw k r)) : Mat k r :=
  NormedSpace.exp (opGen k r v.1) * NormedSpace.exp (unrealify (v.2 : EuclideanSpace ℝ _))

theorem expK_mem (A : lieE (Kw k r)) : NormedSpace.exp (unrealify (A : EuclideanSpace ℝ _)) ∈ Kw k r :=
  exp_mem ((mem_lieE_iff isMatGroup_Kw _).1 A.2)

theorem chart_mem (v : TrE k × lieE (Kw k r)) : chart k r v ∈ UWb k r :=
  HU.uwb_mul (exp_mem (gen_mem _)) (mem_Kw.1 (expK_mem _)).1

theorem strict_prod {A E F : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (J : E →L[ℝ] A) (J' : F →L[ℝ] A) :
    HasStrictFDerivAt (fun v : E × F => NormedSpace.exp (J v.1) * NormedSpace.exp (J' v.2)) (J.coprod J') 0 := by
  refine ((GlobalTheory.ChartDensity.hasStrict_exp (J.comp (ContinuousLinearMap.fst ℝ E F))).mul'
    (GlobalTheory.ChartDensity.hasStrict_exp (J'.comp (ContinuousLinearMap.snd ℝ E F)))).congr_fderiv ?_
  ext v <;> simp

open scoped Matrix.Norms.Operator in
theorem chart_strict (i j : Fin (2 * r + k + 1)) : ∃ D : (TrE k × lieE (Kw k r)) →L[ℝ] ℂ,
    HasStrictFDerivAt (fun x => chart k r x i j) D 0 ∧
      ∀ v, D v = unrealify ((tangEquiv k r v : lieE (UWb k r)) : EuclideanSpace ℝ _) i j := by
  let J : TrE k →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (opGenLin k r)
  let J' : lieE (Kw k r) →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (GlobalTheory.ChartDensity.lieIncl (Kw k r))
  let T : Mat k r →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  refine ⟨T.comp (J.coprod J'), T.hasStrictFDerivAt.comp 0 (strict_prod J J'), fun v => ?_⟩
  change _ = unrealify (tang k r v : EuclideanSpace ℝ _) i j
  rw [coe_tang, unrealify_add]
  rfl

theorem chart_zero : chart k r 0 = 1 := by
  have h : unrealify (0 : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) = 0 := rfl
  simp [chart, opGen_zero, h]

theorem chart_cont : Continuous fun v => (Matrix.of.symm (chart k r v) : Mt k r) := by
  have hexp : Continuous (fun A : Mat k r => NormedSpace.exp A) := by
    open scoped Norms.Operator in exact NormedSpace.exp_continuous
  exact Continuous.matrix_mul (hexp.comp ((continuous_opGen k r).comp continuous_fst))
    ((continuous_expChart k r (Kw k r)).comp continuous_snd)

theorem measurableSet_image_ball {E X : Type} [NormedAddCommGroup E] [ProperSpace E] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {f : E → X} (hf : Continuous f) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball 0 ρ) := by
  have e : Metric.ball (0 : E) ρ = ⋃ n : ℕ, Metric.closedBall 0 (ρ - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Metric.mem_ball, Metric.mem_closedBall, Set.mem_iUnion, dist_zero_right]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [e, Set.image_iUnion]
  exact MeasurableSet.iUnion fun n => ((isCompact_closedBall _ _).image hf).isClosed.measurableSet

theorem hasDens_of_gauge {S : Set (Mat k r)} {ν : Measure (Mt k r)} (h : IsGaugeOn k r S ν) :
    GlobalTheory.Amp.HasDens S ν 1 := by
  have h1 := (ENNReal.continuous_ofReal.tendsto 1).comp h.2
  rw [ENNReal.ofReal_one] at h1
  refine h1.congr' ?_
  filter_upwards [h.2.eventually (lt_mem_nhds one_pos), self_mem_nhdsWithin] with ρ hρ hρ0
  have ht : ν (expBall (k := k) (r := r) S ρ) ≠ ⊤ := fun e => by simp [e] at hρ
  have hv : volume (Metric.ball (0 : lieE S) ρ) ≠ 0 := (Metric.measure_ball_pos _ _ hρ0).ne'
  simp only [Function.comp, sVol]
  rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (ENNReal.div_ne_top ht hv)]
  rfl

theorem box_lim {ν : Measure (Mt k r)} (h : IsGaugeOn k r (UWb k r) ν) :
    Tendsto (fun ρ : ℝ => (ν ((fun v => Matrix.of.symm (chart k r v)) '' Metric.ball 0 ρ)).toReal /
      (tVol k ρ * sVol k r (Kw k r) ρ)) (𝓝[>] 0) (𝓝 1) := by
  have h1 := GlobalTheory.ChartDensity.density_in_chart _ (UWb k r) ν 1 isMatGroup_UWb h.1 (hasDens_of_gauge h)
    (TrE k × lieE (Kw k r)) (chart k r) (tangEquiv k r) chart_zero (Eventually.of_forall chart_mem) chart_strict
  refine ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1).congr fun ρ => ?_
  have e := volume_tang_ball (k := k) (r := r) ρ
  simp only [Function.comp, tVol, sVol]
  rw [← ENNReal.toReal_mul, ← e, ENNReal.toReal_div]
  rfl

theorem orb_eq_iff {T' : ℝ} (hT : 0 < T') {g g' : Mat k r} (hg : g ∈ UWb k r) (hg' : g' ∈ UWb k r) :
    opCo k r (g *ᵥ opBase k r T') = opCo k r (g' *ᵥ opBase k r T') ↔ g *ᵥ wLast k r = g' *ᵥ wLast k r := by
  have hs : (Real.sqrt T' : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  constructor
  · intro h
    funext i
    rw [wLast, MB.mulVec_bvec, MB.mulVec_bvec]
    by_cases hi : MB.mid k r i
    · refine mul_left_cancel₀ hs ?_
      rw [← mulVec_base, ← mulVec_base]
      rcases mid_cases hi with ⟨a, rfl⟩ | rfl
      · exact congrFun (congrArg Prod.fst h) a
      · exact congrArg Prod.snd h
    · rw [op_uwb_row hg i _ hi, op_uwb_row hg' i _ hi]
  · intro h
    rw [opBase, Matrix.mulVec_smul, Matrix.mulVec_smul, h]

theorem psi_injOn {T' : ℝ} (hT : 0 < T') : ∃ ε > 0, Set.InjOn (psiE k r T') (Metric.ball 0 ε) := by
  have hd : (DL k T').det ≠ 0 := by rw [DL_det T' hT]; positivity
  have h : HasStrictFDerivAt (phiT k r T') ((DL k T').toContinuousLinearEquivOfDetNeZero hd : TrE k →L[ℝ] TrE k) 0 :=
    phiT_strict T' hT
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff_ball.1 h.eventually_left_inverse
  refine ⟨ε, hε, fun x hx y hy e => ?_⟩
  rw [← H x hx, ← H y hy, phiT, phiT, e]

theorem tube_eq {T' : ℝ} (hT : 0 < T') {νg νK : Measure (Mt k r)} (hk : 1 ≤ k) (hg : IsGaugeOn k r (UWb k r) νg)
    (hK : IsHaarOn (Kw k r) νK) {ρ : ℝ} (hi : Set.InjOn (psiE k r T') (Metric.ball 0 ρ)) :
    νK Set.univ * νg ((fun v => Matrix.of.symm (chart k r v)) '' Metric.ball 0 ρ) =
      νK (expBall (k := k) (r := r) (Kw k r) ρ) * νg (opOrb k r T' ⁻¹' opE k r T' ρ) := by
  have := hg.1.1
  have := hK.1
  have key : ∀ (g h : Mat k r) (v : TrE k × lieE (Kw k r)), g ∈ UWb k r → h ∈ Kw k r → chart k r v = g * h →
      psiE k r T' v.1 = opCo k r (g *ᵥ opBase k r T') := by
    intro g h v hg hh e
    refine (orb_eq_iff hT (exp_mem (gen_mem _)) hg).2 ?_
    have := congrArg (· *ᵥ wLast k r) e
    simpa only [chart, ← Matrix.mulVec_mulVec, (expK_mem _).2.2, hh.2.2] using this
  refine tube_identity (UWb k r) (Kw k r) νg νK hg.1.2.2.1 hK.2.2.1
    (fun p hp => unimodW k r νg hk hg p (mem_Kw.1 hp).1) hK.2.2.2
    ((continuous_opOrb T').measurable (opEMeas k r T' ρ)) (measurableSet_image_ball chart_cont ρ)
    (measurableSet_expBall k r _ ρ) ?_ ?_
  · rintro g hgG ⟨q, hq, e⟩
    have ha : NormedSpace.exp (opGen k r q) ∈ UWb k r := exp_mem (gen_mem q)
    have hu := HU.uwb_unit ha
    have e' := (orb_eq_iff hT ha hgG).1 e
    refine ⟨(NormedSpace.exp (opGen k r q))⁻¹ * Matrix.of g, mem_Kw.2 ⟨HU.uwb_mul (HU.uwb_inv ha) hgG, ?_⟩,
      fun h hh => ⟨?_, ?_⟩⟩
    · rw [← Matrix.mulVec_mulVec, ← e', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    · rintro ⟨v, hv, ev⟩
      have ev' : chart k r v = Matrix.of g * Matrix.of h := ev
      rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff] at hv
      have hvq : v.1 = q := hi (mem_ball_zero_iff.2 hv.1) hq ((key _ _ v hgG hh ev').trans e.symm)
      refine ⟨v.2, mem_ball_zero_iff.2 hv.2, ?_⟩
      change NormedSpace.exp (unrealify (v.2 : EuclideanSpace ℝ _)) =
        (NormedSpace.exp (opGen k r q))⁻¹ * Matrix.of g * Matrix.of h
      rw [Matrix.mul_assoc, ← ev', chart, hvq, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
    · rintro ⟨A, hA, eA⟩
      have eA' : NormedSpace.exp (unrealify (A : EuclideanSpace ℝ _)) =
        (NormedSpace.exp (opGen k r q))⁻¹ * Matrix.of g * Matrix.of h := eA
      refine ⟨(q, A), ?_, ?_⟩
      · rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
        exact ⟨mem_ball_zero_iff.1 hq, mem_ball_zero_iff.1 hA⟩
      · change chart k r (q, A) = Matrix.of g * Matrix.of h
        rw [chart, eA', Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  · rintro g hgG hn h hh ⟨v, hv, ev⟩
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff] at hv
    exact hn ⟨v.1, mem_ball_zero_iff.2 hv.1, key _ _ v hgG hh ev⟩

theorem tubeLimK : PI.RhsWLim.W.TubeLimK := by
  intro k r T' hk hT νg νK hg hK
  obtain ⟨ε, hε, hi⟩ := psi_injOn (k := k) (r := r) hT
  have h := ((box_lim hg).div hK.2 one_ne_zero).const_mul (νK Set.univ).toReal
  rw [div_one, mul_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε, hK.2.eventually (lt_mem_nhds one_pos)] with ρ hρ hc
  have e := congrArg ENNReal.toReal (tube_eq hT hk hg hK.1 (hi.mono (Metric.ball_subset_ball hρ.2.le)))
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at e
  have ht : 0 < tVol k ρ := ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hρ.1).ne' measure_ball_lt_top.ne
  have hs : 0 < sVol k r (Kw k r) ρ :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ hρ.1).ne' measure_ball_lt_top.ne
  have hc' := (div_pos_iff_of_pos_right hs).1 hc
  simp only [Pi.div_apply]
  field_simp
  exact e

end GlobalTheory.StabTube
