import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddLattice

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col Topology

noncomputable section

theorem tof_box_int_differentiable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {d : ℕ} {G : V → ℂ} (hG : Differentiable ℂ G)
    {φ : (Fin d → ℝ) → V} (hφ : Continuous φ) :
    Differentiable ℂ (fun v => ∫ t in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, G (v + φ t)) := by
  intro x₀
  have hcd : ContDiff ℂ (1 : ℕ) G := contDiff_of_differentiable_fd hG 1
  have hG' : Continuous (fderiv ℂ G) := hcd.continuous_fderiv (by norm_num)
  set B := {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} with hB
  have hBsub : B ⊆ Set.Icc 0 1 := fun x hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hIcc : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
  have hBm : MeasurableSet B := tof_box_measurable d
  have hfin : volume B < ⊤ := (measure_mono hBsub).trans_lt hIcc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hfin.ne
  have hKc : IsCompact ((fun p : V × (Fin d → ℝ) => p.1 + φ p.2) ''
      (Metric.closedBall x₀ 1 ×ˢ Set.Icc 0 1)) :=
    ((isCompact_closedBall x₀ 1).prod hIcc).image (continuous_fst.add (hφ.comp continuous_snd))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hG'.continuousOn
  have hcont : ∀ x, Continuous fun t => G (x + φ t) := fun x =>
    hG.continuous.comp (continuous_const.add hφ)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict B)
    (F := fun v t => G (v + φ t)) (F' := fun v t => fderiv ℂ G (v + φ t)) (x₀ := x₀)
    (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    (((hcont x₀).continuousOn.integrableOn_compact hIcc).mono_set hBsub)
    ((hG'.comp (continuous_const.add hφ)).aestronglyMeasurable)
    ((ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun t ht x hx =>
      hC _ ⟨(x, t), ⟨Metric.ball_subset_closedBall hx, hBsub ht⟩, rfl⟩))
    (integrable_const C)
    (Filter.Eventually.of_forall fun t x _ => by
      have h1 := (hG (x + φ t)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (φ t))
      simp only [ContinuousLinearMap.comp_id] at h1
      exact h1)
  exact h.differentiableAt

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem tb_continuous (hI : IsSplit P I) : Continuous (tb hI) := by
  unfold tb
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

theorem zeroMode_eq_fiber_integral (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    zmC hI s 0 = fun v => ∫ t in {x : Fin (Module.finrank ℝ (IR I)) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      zmG I s (v + tb hI t) := by
  funext v
  simp [zmC, zmBox]
  rfl

theorem zeroMode_differentiable (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Differentiable ℂ (zmC hI s 0) := by
  have hz : ∀ k, Differentiable ℂ (fun v : Vsp X.dim => Col.z (IR I) k v) := by
    intro k
    unfold Col.z Hf
    exact Differentiable.fun_sum fun i _ =>
      ((EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable).mul_const _
  have hS : Differentiable ℂ (fun v => Col.S (IR I) v) := by
    unfold Col.S
    exact Differentiable.fun_sum fun k _ => (hz k).pow 2
  have hG : Differentiable ℂ (zmG I s) := by
    unfold zmG
    exact (hs.1.comp (differentiable_pi.2 fun _ => differentiable_id)).mul
      ((differentiable_const _).mul hS).cexp
  rw [zeroMode_eq_fiber_integral hI s]
  exact tof_box_int_differentiable hG (tb_continuous hI)

theorem zeroMode_add_real_direction (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (w : Vsp X.dim) (k : Fin (dK (IR I))) (ζ : ℂ) :
    zmC hI s 0 (w + ζ • e (IR I) k) = zmC hI s 0 w := by
  set ψ : ℂ → ℂ := fun ζ => zmC hI s 0 (w + ζ • e (IR I) k) with hψ
  have hdiff : Differentiable ℂ ψ :=
    (zeroMode_differentiable hI hs).comp ((differentiable_const _).add (differentiable_id.smul_const _))
  have hreal : ∀ ζ (t : ℝ), ψ (ζ + t) = ψ ζ := fun ζ t => by
    simp only [hψ]
    rw [add_smul, ← add_assoc, show ((t : ℂ)) • e (IR I) k = t • e (IR I) k from
      (Complex.coe_smul t _)]
    exact zeroMode_add_realSpan hI hs _ (Submodule.smul_mem _ _ (e_mem _ k))
  have hder : ∀ ζ, deriv ψ ζ = 0 := fun ζ => by
    have h1 : HasDerivAt (fun z => ψ (ζ + z)) (deriv ψ ζ) ((0 : ℝ) : ℂ) := by
      have := (hdiff (ζ + ((0 : ℝ) : ℂ))).hasDerivAt
      simpa using (this.comp_const_add ζ ((0 : ℝ) : ℂ))
    have h2 := h1.comp_ofReal
    have h3 : (fun y : ℝ => ψ (ζ + (y : ℂ))) = fun _ => ψ ζ := funext fun y => hreal ζ y
    rw [h3] at h2
    exact (h2.unique (hasDerivAt_const _ _)).symm ▸ rfl
  have := is_const_of_deriv_eq_zero hdiff hder ζ 0
  simpa [hψ] using this

theorem zeroMode_proj_two (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) : zmC hI s 0 v = zmC hI s 0 (p2 (IR I) v) := by
  have hL : ∀ (L : Finset (Fin (dK (IR I)))) (c : Fin (dK (IR I)) → ℂ) (w : Vsp X.dim),
      zmC hI s 0 (w + ∑ k ∈ L, c k • e (IR I) k) = zmC hI s 0 w := by
    intro L c w
    induction L using Finset.induction_on with
    | empty => simp
    | insert a L ha ih =>
      rw [Finset.sum_insert ha, add_comm (c a • e (IR I) a), ← add_assoc, zeroMode_add_real_direction hI hs, ih]
  have hp : p2 (IR I) v = v + ∑ k, (-(z (IR I) k v)) • e (IR I) k := by
    simp only [p2, p1, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hp, hL]

theorem proj_two_embedding (t : EuclideanSpace ℂ (Fin (gB (IR I)))) : p2 (IR I) (jj (IR I) t) = jj (IR I) t := by
  have hmem : jj (IR I) t ∈ V2 (IR I) := ((ob2 (IR I)).repr.symm t).2
  have hz : ∀ k, z (IR I) k (jj (IR I) t) = 0 := by
    intro k
    have h0 : inner ℂ (e (IR I) k) (jj (IR I) t) = 0 :=
      (Submodule.mem_orthogonal _ _).1 hmem _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [PiLp.inner_apply] at h0
    simp only [z, Hf]
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  simp only [p2, p1, hz, zero_smul, Finset.sum_const_zero, sub_zero]

theorem jj_differentiable : Differentiable ℂ (jj (IR I)) := by
  exact ((V2 (IR I)).subtypeL.comp
    ((ob2 (IR I)).repr.symm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin (gB (IR I))) →L[ℂ] V2 (IR I))).differentiable

end ZM

open ZM in
theorem zeroMode_mem_sections [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ZM.zmB hI s ∈ (Col.YB hI hP 1).Sec 1 := by
  have hK := hK_of hI
  refine ⟨(zeroMode_differentiable hI hs).comp jj_differentiable, fun γ hγ t => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 ((YB_lat hI hP 1).1 hγ)
  simp only [zmB]
  rw [jj_add, jj_wmap' hK]
  have hp1 : p1 (IR I) x ∈ IR I := proj_one_mem_realSpan hx
  rw [← zeroMode_add_realSpan hI hs (jj (IR I) t + p2 (IR I) x) hp1,
    show jj (IR I) t + p2 (IR I) x + p1 (IR I) x = jj (IR I) t + x by rw [p2]; abel]
  rw [zeroMode_add_lattice hI hs hx, proj_two_embedding, YB_ka hI hP 1 hx, pow_one]
  have h1 : Hf t (wmap (IR I) x) = Hf (jj (IR I) t) (p2 (IR I) x) := by
    conv_lhs => rw [← wmap_jj (IR I) t]
    rw [Hf_wmap hK, proj_two_embedding]
  have h2 : Hf (wmap (IR I) x) (wmap (IR I) x) = Hf (p2 (IR I) x) (p2 (IR I) x) := Hf_wmap hK x x
  simp only [Nat.cast_one, one_mul]
  rw [h1, h2]

end

end ReciprocityTheory.ChartRestriction.G.I2
