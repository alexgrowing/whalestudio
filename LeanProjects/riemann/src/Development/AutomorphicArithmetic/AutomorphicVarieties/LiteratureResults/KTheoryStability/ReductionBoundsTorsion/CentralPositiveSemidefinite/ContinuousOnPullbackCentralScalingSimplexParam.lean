import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.AvCongr

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

def Smp (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

theorem smp_closed (q : ℕ) : IsClosed (Smp q) := by
  have h1 : IsClosed {t : Fin q → ℝ | ∀ j, 0 ≤ t j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have h2 : IsClosed {t : Fin q → ℝ | ∑ j, t j ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
  exact h1.inter h2

theorem smp_compact (q : ℕ) : IsCompact (Smp q) := by
  refine (isCompact_Icc (a := (0 : Fin q → ℝ)) (b := 1)).of_isClosed_subset (smp_closed q) ?_
  rintro t ⟨h0, h1⟩
  refine ⟨fun j => h0 j, fun j => ?_⟩
  show t j ≤ 1
  calc t j ≤ ∑ i, t i := Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ j)
    _ ≤ 1 := h1

theorem cont_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ}
    {f : ℝ → (Fin n → ℝ) → E} {s : Set (Fin n → ℝ)} (hs : IsCompact s) (hsm : MeasurableSet s)
    (hf : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => f p.1 p.2) (Set.univ ×ˢ s)) :
    Continuous fun x => ∫ y in s, f x y := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := x₀ - 1) (b := x₀ + 1)).prod hs).bddAbove_image
    (hf.norm.mono (Set.prod_mono (Set.subset_univ _) le_rfl))
  have hsec : ∀ y ∈ s, Continuous fun x => f x y := fun y hy => by
    have h := hf.comp (s := Set.univ) (Continuous.continuousOn (by fun_prop : Continuous fun x : ℝ => (x, y)))
      (fun (x : ℝ) _ => ⟨trivial, hy⟩)
    exact continuousOn_univ.mp h
  apply continuousAt_of_dominated (bound := fun _ => M)
  · filter_upwards with x
    exact ContinuousOn.aestronglyMeasurable
      (hf.comp (s := s) (Continuous.continuousOn (by fun_prop : Continuous fun y : Fin n → ℝ => (x, y)))
        (fun (y : Fin n → ℝ) hy => ⟨trivial, hy⟩)) hsm
  · filter_upwards [Icc_mem_nhds (by linarith : x₀ - 1 < x₀) (by linarith : x₀ < x₀ + 1)] with x hx
    rw [ae_restrict_iff' hsm]
    filter_upwards with y hy
    exact hM ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · exact integrableOn_const hs.measure_ne_top
  · rw [ae_restrict_iff' hsm]
    filter_upwards with y hy
    exact (hsec y hy).continuousAt

theorem fubini_smp {q : ℕ} {Φ : ℝ → (Fin q → ℝ) → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × (Fin q → ℝ) => Φ p.1 p.2) (Set.univ ×ˢ Smp q)) :
    ∫ t in Smp q, ∫ τ in (0 : ℝ)..1, Φ τ t = ∫ τ in (0 : ℝ)..1, ∫ t in Smp q, Φ τ t := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have hint : IntegrableOn (fun p : (Fin q → ℝ) × ℝ => Φ p.2 p.1) (Smp q ×ˢ Set.Icc (0 : ℝ) 1) := by
    refine ContinuousOn.integrableOn_compact ((smp_compact q).prod isCompact_Icc) ?_
    exact hΦ.comp (s := Smp q ×ˢ Set.Icc (0 : ℝ) 1)
      (Continuous.continuousOn (by fun_prop : Continuous fun p : (Fin q → ℝ) × ℝ => (p.2, p.1)))
      (fun p hp => ⟨trivial, hp.1⟩)
  have hint' : Integrable (Function.uncurry fun (t : Fin q → ℝ) (τ : ℝ) => Φ τ t)
      ((volume.restrict (Smp q)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hint.mono_set (Set.prod_mono le_rfl Set.Ioc_subset_Icc_self)
  exact integral_integral_swap hint'

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem intS_lin {q : ℕ} (ω : Form (HS L N) q) (A : HS L N →L[ℝ] HS L N) (Y : Fin (q + 1) → HS L N) :
    intS ω (fun j => A (Y j)) = intS (fun h => (ω (A h)).compContinuousLinearMap A) Y := by
  unfold intS
  congr 1
  ext t
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, map_add, map_sum, map_smul, map_sub,
    Function.comp_def]

section One

variable {q : ℕ} (v : InfinitePlace L → ℝ) (ω : Form (HS L N) q)

theorem continuousOn_pullback_centralScaling_line (hcont : Continuous fun t : InfinitePlace L → ℝ => actL (sc t : Gp L N))
    (hc : ContinuousOn ω (Pos L N)) :
    ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N) := by
  have hA : Continuous fun p : ℝ × HS L N => actL (sc (p.1 • v) : Gp L N) :=
    hcont.comp (by fun_prop : Continuous fun p : ℝ × HS L N => p.1 • v)
  have hpt : ContinuousOn (fun p : ℝ × HS L N => ω (actL (sc (p.1 • v) : Gp L N) p.2)) (Set.univ ×ˢ Pos L N) :=
    hc.comp (hA.clm_apply continuous_snd).continuousOn
      (fun p hp => ((sc (p.1 • v) : Gp L N) • (⟨p.2, hp.2⟩ : Pos L N)).2)
  have hB := ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM (𝕜 := ℝ)).comp hA).continuousOn.clm_apply hpt
  unfold pb
  exact hB

variable {v ω}

theorem continuous_pullback_centralScaling_line_apply (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N))
    {h : HS L N} (hh : h ∈ Pos L N) : Continuous fun τ : ℝ => pb (sc (τ • v)) ω h := by
  have hcomp := F1.comp (s := Set.univ) (Continuous.continuousOn (by fun_prop : Continuous fun τ : ℝ => (τ, h)))
    (fun τ _ => ⟨trivial, hh⟩)
  exact continuousOn_univ.mp hcomp

theorem av_cont (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N)) :
    ContinuousOn (av v ω) (Pos L N) := by
  rw [continuousOn_iff_continuous_restrict]
  have hg : Continuous fun p : Pos L N × ℝ => ((p.2, (p.1 : HS L N)) : ℝ × HS L N) := by fun_prop
  have hm : ∀ p : Pos L N × ℝ, ((p.2, (p.1 : HS L N)) : ℝ × HS L N) ∈ Set.univ ×ˢ Pos L N :=
    fun p => Set.mk_mem_prod trivial p.1.2
  have h0 := F1.comp_continuous hg hm
  rw [Function.comp_def] at h0
  have h1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : Pos L N) (τ : ℝ) => pb (sc (τ • v)) ω x.1) (μ := volume) h0 0 1
  exact h1

private theorem pb_pb_apply_eq_pb_mul {q : ℕ} (g k : Gp L N) (ω : Form (HS L N) q) (h : HS L N) :
    pb g (pb k ω) h = pb (k * g) ω h := by
  unfold pb
  ext u
  simp [actL_mul, Function.comp_def]

theorem av_comm (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N))
    (g : Gp L N) (hg : ∀ t, sc t * g = g * sc t) (h : HS L N) (hh : h ∈ Pos L N) :
    pb g (av v ω) h = av v (pb g ω) h := by
  have hgh : actL g h ∈ Pos L N := (g • (⟨h, hh⟩ : Pos L N)).2
  have hint : IntervalIntegrable (fun τ : ℝ => pb (sc (τ • v)) ω (actL g h)) volume 0 1 :=
    (continuous_pullback_centralScaling_line_apply F1 hgh).intervalIntegrable 0 1
  have e1 : pb g (av v ω) h =
      ContinuousAlternatingMap.compContinuousLinearMapCLM (actL g) (av v ω (actL g h)) := rfl
  have e2 : av v ω (actL g h) = ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω (actL g h) := rfl
  have e3 : av v (pb g ω) h = ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) (pb g ω) h := rfl
  rw [e1, e2, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint, e3]
  congr 1
  funext τ
  show pb g (pb (sc (τ • v)) ω) h = pb (sc (τ • v)) (pb g ω) h
  rw [pb_pb_apply_eq_pb_mul, pb_pb_apply_eq_pb_mul, hg]

theorem av_per (hadd : ∀ t t' : InfinitePlace L → ℝ, (sc (t + t') : Gp L N) = sc t * sc t')
    (hcomm : ∀ (t : InfinitePlace L → ℝ) (x : Gp L N), sc t * x = x * sc t)
    (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N))
    (hv : v ∈ Fix ω) (σ : ℝ) : σ • v ∈ Fix (av v ω) := by
  show ∀ h ∈ Pos L N, pb (sc (σ • v)) (av v ω) h = av v ω h
  intro h hh
  rw [av_comm F1 _ (fun t => hcomm t _) h hh]
  show ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) (pb (sc (σ • v)) ω) h = ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω h
  have ep : ∀ τ : ℝ, pb (sc (τ • v)) (pb (sc (σ • v)) ω) h = pb (sc ((τ + σ) • v)) ω h := fun τ => by
    rw [pb_pb_apply_eq_pb_mul, ← hadd, add_smul, add_comm (τ • v)]
  have hper : Function.Periodic (fun τ : ℝ => pb (sc (τ • v)) ω h) 1 := fun τ => by
    show pb (sc ((τ + 1) • v)) ω h = pb (sc (τ • v)) ω h
    have hs : actL (sc (τ • v) : Gp L N) h ∈ Pos L N := ((sc (τ • v) : Gp L N) • (⟨h, hh⟩ : Pos L N)).2
    have hvh : pb (sc v) ω (actL (sc (τ • v) : Gp L N) h) = ω (actL (sc (τ • v) : Gp L N) h) := hv _ hs
    rw [add_smul, one_smul, hadd, hcomm, ← pb_pb_apply_eq_pb_mul]
    show (pb (sc v) ω (actL (sc (τ • v) : Gp L N) h)).compContinuousLinearMap (actL (sc (τ • v) : Gp L N)) =
      (ω (actL (sc (τ • v) : Gp L N) h)).compContinuousLinearMap (actL (sc (τ • v) : Gp L N))
    rw [hvh]
  simp only [ep]
  rw [intervalIntegral.integral_comp_add_right (fun τ => pb (sc (τ • v)) ω h) σ, zero_add, add_comm 1 σ,
    hper.intervalIntegral_add_eq σ 0, zero_add]

theorem simplexIntegral_centralScaling_smul_eq_param (y : Fin (q + 1) → Pos L N) (τ : ℝ) : intP ω (fun j => (sc (τ • v) : Gp L N) • y j) =
    ∫ t in Smp q, pb (sc (τ • v)) ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1))
      (fun j => (y j.succ).1 - (y 0).1) := by
  show intS ω (fun j => actL (sc (τ • v) : Gp L N) (y j).1) = _
  rw [intS_lin]
  rfl

theorem continuousOn_pullback_centralScaling_simplexParam (hmem : ∀ (y : Fin (q + 1) → Pos L N) (t : Fin q → ℝ), (∀ j, 0 ≤ t j) → ∑ j, t j ≤ 1 →
      (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) ∈ Pos L N)
    (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N))
    (y : Fin (q + 1) → Pos L N) : ContinuousOn (fun p : ℝ × (Fin q → ℝ) =>
      pb (sc (p.1 • v)) ω ((y 0).1 + ∑ j, p.2 j • ((y j.succ).1 - (y 0).1))
        (fun j => (y j.succ).1 - (y 0).1)) (Set.univ ×ˢ Smp q) := by
  have hφ : Continuous fun p : ℝ × (Fin q → ℝ) =>
      ((p.1, (y 0).1 + ∑ j, p.2 j • ((y j.succ).1 - (y 0).1)) : ℝ × HS L N) := by fun_prop
  have hc := F1.comp (s := Set.univ ×ˢ Smp q) hφ.continuousOn
    (fun (p : ℝ × (Fin q → ℝ)) (hp : p ∈ Set.univ ×ˢ Smp q) =>
      Set.mk_mem_prod trivial (hmem y p.2 hp.2.1 hp.2.2))
  rw [Function.comp_def] at hc
  have hd := (ContinuousAlternatingMap.apply ℝ (HS L N) ℝ (fun j => (y j.succ).1 - (y 0).1)).continuous.comp_continuousOn hc
  rw [Function.comp_def] at hd
  simpa only [ContinuousAlternatingMap.apply_apply] using hd

theorem av_int (hmem : ∀ (y : Fin (q + 1) → Pos L N) (t : Fin q → ℝ), (∀ j, 0 ≤ t j) → ∑ j, t j ≤ 1 →
      (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) ∈ Pos L N)
    (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N))
    (y : Fin (q + 1) → Pos L N) :
    intP (av v ω) y = ∫ τ in (0 : ℝ)..1, intP ω fun j => (sc (τ • v) : Gp L N) • y j := by
  show ∫ t in Smp q, av v ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1)) (fun j => (y j.succ).1 - (y 0).1) = _
  have e : ∀ t ∈ Smp q, av v ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1)) (fun j => (y j.succ).1 - (y 0).1)
      = ∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1))
          (fun j => (y j.succ).1 - (y 0).1) := by
    intro t ht
    have hint := (continuous_pullback_centralScaling_line_apply F1 (hmem y t ht.1 ht.2)).intervalIntegrable (μ := volume) 0 1
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousAlternatingMap.apply ℝ (HS L N) ℝ (fun j => (y j.succ).1 - (y 0).1)) hint).symm
  rw [setIntegral_congr_fun (smp_closed q).measurableSet e, fubini_smp (continuousOn_pullback_centralScaling_simplexParam hmem F1 y)]
  congr 1
  funext τ
  rw [simplexIntegral_centralScaling_smul_eq_param]

theorem av_fr (F1 : ContinuousOn (fun p : ℝ × HS L N => pb (sc (p.1 • v)) ω p.2) (Set.univ ×ˢ Pos L N))
    (x : Gp L N) : fr (av v ω) x = ∫ τ in (0 : ℝ)..1, fr ω (sc (τ • v) * x) := by
  have hx : actL x (one L N).1 ∈ Pos L N := (x • one L N).2
  have hint := (continuous_pullback_centralScaling_line_apply F1 hx).intervalIntegrable (μ := volume) 0 1
  have e1 : fr (av v ω) x = ContinuousAlternatingMap.compContinuousLinearMapCLM (actL x)
      (∫ τ in (0:ℝ)..1, pb (sc (τ • v)) ω (actL x (one L N).1)) := rfl
  rw [e1, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext τ
  show pb x (pb (sc (τ • v)) ω) (one L N).1 = pb (sc (τ • v) * x) ω (one L N).1
  rw [pb_pb_apply_eq_pb_mul]

end One

theorem tAv_of (hSc : TScal) (hSi : TSimp) : TAv := by
  unfold TScal at hSc
  unfold TSimp at hSi
  unfold TAv
  intro L _ _ N q v ω hc
  obtain ⟨hadd, hcomm, -, -, hcont⟩ := hSc L N
  obtain ⟨hmem, -⟩ := hSi L N q
  have F1 := continuousOn_pullback_centralScaling_line v ω hcont hc
  refine ⟨av_cont F1, fun g hg h hh => av_comm F1 g hg h hh, fun hv σ => av_per hadd hcomm F1 hv σ,
    fun y => ?_, fun y => av_int hmem F1 y, fun x => av_fr F1 x⟩
  have e : (fun τ : ℝ => intP ω fun j => (sc (τ • v) : Gp L N) • y j) = fun τ =>
      ∫ t in Smp q, pb (sc (τ • v)) ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1))
        (fun j => (y j.succ).1 - (y 0).1) := funext fun τ => simplexIntegral_centralScaling_smul_eq_param y τ
  rw [e]
  exact cont_param (smp_compact q) (smp_closed q).measurableSet (continuousOn_pullback_centralScaling_simplexParam hmem F1 y)

end PositivityTheory.KB.CentralizerFixed

end
