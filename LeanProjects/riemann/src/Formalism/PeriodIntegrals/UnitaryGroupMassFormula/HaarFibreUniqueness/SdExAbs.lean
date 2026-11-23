import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SmulMemHermR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExChar

noncomputable section

namespace PI.OmFibreUniq.W.SdAbs

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
open PI.VolStabSW.SdUniqW PI.OmFibreUniq.W.SdCore PI.OmFibreUniq.W.SdChar
open scoped ENNReal

section Abs

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v)

theorem B_zero_left (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (y : V) : B 0 y = 0 := by
  have := hBs 0 0 y
  rwa [zero_smul, zero_mul] at this

theorem B_sum_left (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} (s : Finset ι) (f : ι → V)
    (y : V) : B (∑ i ∈ s, f i) y = ∑ i ∈ s, B (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B_zero_left v B hBs]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hBa, ih]

theorem B_expand (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} [Fintype ι] (β β' : ι → V)
    (h1 : ∀ x, x = ∑ j, B x (β' j) • β j) (x y : V) :
    B x y = ∑ j, B x (β' j) * B (β j) y := by
  have e := congrArg (fun x' => B x' y) (h1 x)
  rw [e, B_sum_left v B hBa hBs]
  exact Finset.sum_congr rfl fun j _ => hBs _ _ _

theorem B_cont (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBc : ∀ x, Continuous (B x)) {ι : Type} [Fintype ι] (β β' : ι → V)
    (h1 : ∀ x, x = ∑ j, B x (β' j) • β j) : Continuous (fun p : V × V => B p.1 p.2) := by
  have e : (fun p : V × V => B p.1 p.2) = fun p => ∑ j, B (β' j) p.1 * B (β j) p.2 := by
    funext p
    rw [B_expand v B hBa hBs β β' h1]
    exact Finset.sum_congr rfl fun j _ => by rw [hBsym p.1 (β' j)]
  rw [e]
  exact continuous_finset_sum _ fun j _ =>
    ((hBc (β' j)).comp continuous_fst).mul ((hBc (β j)).comp continuous_snd)

def M0 (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} (β' : ι → V) : AddSubgroup V where
  carrier := {x | ∀ j, B x (β' j) ∈ v.adicCompletionIntegers F}
  add_mem' := fun {a b} ha hb j => by
    simp only [Set.mem_setOf_eq] at *
    rw [hBa]
    exact add_mem (ha j) (hb j)
  zero_mem' := fun j => by
    show B 0 (β' j) ∈ _
    rw [B_zero_left v B hBs]
    exact zero_mem _
  neg_mem' := fun {a} ha j => by
    simp only [Set.mem_setOf_eq] at *
    rw [← neg_one_smul (Fv F v) a, hBs]
    exact mul_mem (neg_mem (one_mem _)) (ha j)

theorem mem_dual_integral_module (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} (β' : ι → V) (x : V) :
    x ∈ M0 v B hBa hBs β' ↔ ∀ j, B x (β' j) ∈ v.adicCompletionIntegers F := Iff.rfl

theorem smul_mem_dual_integral_module (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) {ι : Type} (β' : ι → V) {c : Fv F v}
    (hc : c ∈ v.adicCompletionIntegers F) {x : V} (hx : x ∈ M0 v B hBa hBs β') :
    c • x ∈ M0 v B hBa hBs β' := fun j => by
  rw [hBs]
  exact mul_mem hc (hx j)

theorem isOpen_dual_integral_module (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBc : ∀ x, Continuous (B x)) {ι : Type} [Fintype ι] (β' : ι → V) :
    IsOpen (M0 v B hBa hBs β' : Set V) := by
  have e : (M0 v B hBa hBs β' : Set V) =
      ⋂ j, (fun x => B x (β' j)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x; simp [mem_dual_integral_module]
  rw [e]
  exact isOpen_iInter_of_finite fun j =>
    (Valued.isOpen_valuationSubring _).preimage ((hBc (β' j)).congr fun x => hBsym _ _)

theorem isCompact_dual_integral_module (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBc : ∀ x, Continuous (B x)) {ι : Type} [Fintype ι] (β β' : ι → V)
    (h1 : ∀ x, x = ∑ j, B x (β' j) • β j) :
    IsCompact (M0 v B hBa hBs β' : Set V) := by
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hK : IsCompact ((fun c : ι → Fv F v => ∑ j, c j • β j) ''
      Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    (isCompact_univ_pi fun _ => hO).image
      (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)
  have hcl : IsClosed (M0 v B hBa hBs β' : Set V) :=
    AddSubgroup.isClosed_of_isOpen _ (isOpen_dual_integral_module v B hBa hBs hBsym hBc β')
  refine hK.of_isClosed_subset hcl fun x hx => ⟨fun j => B x (β' j), fun j _ => hx j, ?_⟩
  exact (h1 x).symm

theorem haar_smul_preimage (μ0 : Measure V) [μ0.IsAddHaarMeasure] (a : Fv F v) (ha : a ≠ 0) :
    ∃ c : ℝ≥0∞, ∀ S, MeasurableSet S → μ0 ((fun y : V => a • y) ⁻¹' S) = c * μ0 S := by
  let e : V ≃+ V := (LinearEquiv.smulOfNeZero (Fv F v) V a ha).toAddEquiv
  have he : Continuous e := by
    show Continuous fun y : V => a • y
    exact continuous_const_smul a
  have hes : Continuous e.symm := by
    show Continuous fun y : V => a⁻¹ • y
    exact continuous_const_smul a⁻¹
  haveI := AddEquiv.isAddHaarMeasure_map μ0 e he hes
  refine ⟨(Measure.addHaarScalarFactor (μ0.map e) μ0 : ℝ≥0∞), fun S hS => ?_⟩
  have hmap : μ0.map e = Measure.addHaarScalarFactor (μ0.map e) μ0 • μ0 :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have h := Measure.map_apply (μ := μ0) he.measurable hS
  rw [hmap, Measure.smul_apply] at h
  show μ0 (e ⁻¹' S) = _
  rw [← h]
  rfl

theorem absSd_main (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
    (hψn : ∀ r, ‖ψ0 r‖ = 1) (hnt : ∃ y, ψ0 y ≠ 1)
    (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBc : ∀ x, Continuous (B x)) {ι : Type} [Fintype ι] (β β' : ι → V)
    (h1 : ∀ x, x = ∑ j, B x (β' j) • β j) (h2 : ∀ y, y = ∑ j, B (β j) y • β' j) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ0 (B x y)) := by
  obtain ⟨π, hπ0, hπt, -⟩ := PI.VolStabSW.exists_unif_Fv v
  set χ : V → V → ℂ := fun x y => ψ0 (B x y) with hχdef
  have hχc : Continuous (fun p : V × V => χ p.1 p.2) :=
    hψc.comp (B_cont v B hBa hBs hBsym hBc β β' h1)
  have hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y := fun x t y => by
    simp only [hχdef]; rw [hBa, hψa]
  have hsym : ∀ x y, χ x y = χ y x := fun x y => by simp only [hχdef]; rw [hBsym]
  have hn : ∀ x y, ‖χ x y‖ = 1 := fun x y => hψn _
  set L := M0 v B hBa hBs β' with hLdef
  have hLo : IsOpen (L : Set V) := isOpen_dual_integral_module v B hBa hBs hBsym hBc β'
  have hLc : IsCompact (L : Set V) := isCompact_dual_integral_module v B hBa hBs hBsym hBc β β' h1
  have hBzr : ∀ x, B x 0 = 0 := fun x => by rw [hBsym]; exact B_zero_left v B hBs x

  have hQsub : ∀ q : V, (∀ j, B (β j) q ∈ Aset v ψ0) → q ∈ ann χ L := by
    intro q hq x hx
    show ψ0 (B x q) = 1
    rw [B_expand v B hBa hBs β β' h1, psi_sum v ψ0 hψa hψn]
    exact Finset.prod_eq_one fun j _ => hq j _ (hx j)
  have hQ : {q : V | ∀ j, B (β j) q ∈ Aset v ψ0} ∈ 𝓝 (0 : V) := by
    have hj : ∀ j, {q : V | B (β j) q ∈ Aset v ψ0} ∈ 𝓝 (0 : V) := fun j =>
      (hBc (β j)).continuousAt.preimage_mem_nhds
        (by rw [hBzr]; exact Aset_mem_nhds v ψ0 hψc hψa hψn)
    have e : {q : V | ∀ j, B (β j) q ∈ Aset v ψ0} = ⋂ j, {q : V | B (β j) q ∈ Aset v ψ0} := by
      ext; simp
    rw [e]
    exact Filter.iInter_mem.2 hj
  have hNo0 : IsOpen (ann χ (L : Set V)) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
      have := (continuous_sub_right y).tendsto y
      rwa [sub_self] at this
    filter_upwards [ht hQ] with y' hy'
    intro x hx
    have hq := hQsub _ hy' x hx
    have hyx := hy x hx
    show ψ0 (B x y') = 1
    have e1 : y' = y + (y' - y) := by abel
    rw [e1, hBsym, hBa, hψa, hBsym y, hBsym (y' - y)]
    rw [show ψ0 (B x y) = 1 from hyx, show ψ0 (B x (y' - y)) = 1 from hq, one_mul]
  have hNcl : IsClosed (ann χ (L : Set V)) := isClosed_ann χ hχc L

  have hNc0 : IsCompact (ann χ (L : Set V)) := by
    obtain ⟨y0, hy0, hA⟩ := Aset_bdd v ψ0 hψa hψn hnt
    have hev : ∀ᶠ N in atTop, ∀ j l, π ^ N * B (β j) (β' l) ∈ v.adicCompletionIntegers F := by
      rw [Filter.eventually_all]
      intro j
      rw [Filter.eventually_all]
      intro l
      have : Tendsto (fun N => π ^ N * B (β j) (β' l)) atTop (𝓝 0) := by
        simpa using hπt.mul_const (B (β j) (β' l))
      exact this.eventually_mem ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))
    obtain ⟨N, hN⟩ := hev.exists
    have hπN : π ^ N ≠ 0 := pow_ne_zero _ hπ0
    have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
      PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
    have hK : IsCompact ((fun c : ι → Fv F v => ∑ j, ((π ^ N)⁻¹ * y0 * c j) • β' j) ''
        Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
      (isCompact_univ_pi fun _ => hO).image
        (continuous_finset_sum _ fun j _ =>
          (continuous_const.mul (continuous_apply j)).smul continuous_const)
    refine hK.of_isClosed_subset hNcl fun y hy => ?_
    have hin : ∀ j, π ^ N * B (β j) y ∈ Aset v ψ0 := by
      intro j c hc
      have hm : (c * π ^ N) • β j ∈ L := fun l => by
        show B ((c * π ^ N) • β j) (β' l) ∈ _
        rw [hBs, mul_assoc]
        exact mul_mem hc (hN j l)
      have := hy _ hm
      simp only [hχdef] at this
      rwa [hBs, mul_assoc] at this
    choose s hs hts using fun j => hA _ (hin j)
    refine ⟨s, fun j _ => hs j, ?_⟩
    simp only
    conv_rhs => rw [h2 y]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [mul_assoc, ← hts j, ← mul_assoc, inv_mul_cancel₀ hπN, one_mul]

  set M : ℕ → AddSubgroup V := fun k => L.comap (DistribMulAction.toAddMonoidHom V (π ^ k))
    with hMdef
  have hMset : ∀ k, (M k : Set V) = (fun x => π ^ k • x) ⁻¹' (L : Set V) := fun k => rfl
  have hπk : ∀ k, π ^ k ≠ 0 := fun k => pow_ne_zero k hπ0
  have hann : ∀ k, ann χ (M k : Set V) = (fun y => (π ^ k)⁻¹ • y) ⁻¹' ann χ (L : Set V) := by
    intro k
    ext y
    constructor
    · intro hy x hx
      have hx' : (π ^ k)⁻¹ • x ∈ (M k : Set V) := by
        show π ^ k • ((π ^ k)⁻¹ • x) ∈ L
        rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul]
      have := hy _ hx'
      simp only [hχdef] at this ⊢
      rwa [hBs, hBsym, ← hBs, hBsym] at this
    · intro hy x hx
      have := hy _ hx
      change ψ0 (B (π ^ k • x) ((π ^ k)⁻¹ • y)) = 1 at this
      simp only [hχdef]
      rwa [hBs, hBsym, hBs, hBsym, ← mul_assoc, mul_inv_cancel₀ (hπk k), one_mul] at this
  have hMo : ∀ k, IsOpen (M k : Set V) := fun k => by
    rw [hMset]; exact hLo.preimage (continuous_const_smul _)
  have hMc : ∀ k, IsCompact (M k : Set V) := fun k => by
    rw [hMset]
    exact (Homeomorph.smulOfNeZero (π ^ k) (hπk k)).isCompact_preimage.2 hLc
  have hNo : ∀ k, IsOpen (ann χ (M k : Set V)) := fun k => by
    rw [hann]; exact hNo0.preimage (continuous_const_smul _)
  have hNc : ∀ k, IsCompact (ann χ (M k : Set V)) := fun k => by
    rw [hann]
    exact (Homeomorph.smulOfNeZero ((π ^ k)⁻¹) (inv_ne_zero (hπk k))).isCompact_preimage.2 hNc0
  have hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k := by
    intro y
    have ht : Tendsto (fun k => π ^ k • y) atTop (𝓝 0) := by simpa using hπt.smul_const y
    exact (ht.eventually_mem (hLo.mem_nhds L.zero_mem)).mono fun k hk => hk
  have hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k : Set V) ⊆ U := by
    intro U hU
    have hP : ∀ w ∈ ann χ (L : Set V), ∀ᶠ z : Fv F v × V in 𝓝 ((0 : Fv F v), w), z.1 • z.2 ∈ U :=
      fun w _ => (continuous_smul.tendsto ((0 : Fv F v), w)).eventually_mem
        (by rw [show ((0 : Fv F v), w).1 • ((0 : Fv F v), w).2 = (0 : V) by simp]; exact hU)
    have hev := hNc0.eventually_forall_of_forall_eventually (P := fun c w => c • w ∈ U) hP
    filter_upwards [hπt.eventually hev] with k hk y hy
    rw [hann] at hy
    have := hk _ hy
    rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul] at this

  let μ0 : Measure V := Measure.addHaar
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hNm : MeasurableSet (ann χ (L : Set V)) := hNcl.measurableSet
  have hL0 : μ0 (L : Set V) ≠ 0 := (hLo.measure_pos μ0 ⟨0, L.zero_mem⟩).ne'
  have hLt : μ0 (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hgen : ∀ k, μ0 (M k : Set V) * μ0 (ann χ (M k : Set V)) =
      μ0 (L : Set V) * μ0 (ann χ (L : Set V)) := by
    intro k
    obtain ⟨c1, hc1⟩ := haar_smul_preimage v μ0 (π ^ k) (hπk k)
    obtain ⟨c2, hc2⟩ := haar_smul_preimage v μ0 ((π ^ k)⁻¹) (inv_ne_zero (hπk k))
    have hid : (fun y : V => (π ^ k)⁻¹ • y) ⁻¹' ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) =
        (L : Set V) := by
      ext y; simp [smul_smul, mul_inv_cancel₀ (hπk k)]
    have hm1 : MeasurableSet ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) :=
      hLm.preimage (continuous_const_smul _).measurable
    have h12 : c2 * c1 = 1 := by
      have := hc2 _ hm1
      rw [hid, hc1 _ hLm, ← mul_assoc] at this
      have h3 : μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ = 1 := ENNReal.mul_inv_cancel hL0 hLt
      calc c2 * c1 = c2 * c1 * μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ := by
            rw [mul_assoc (c2 * c1), h3, mul_one]
        _ = 1 := by rw [← this, h3]
    rw [hann, hMset, hc1 _ hLm, hc2 _ hNm]
    calc c1 * μ0 (L : Set V) * (c2 * μ0 (ann χ (L : Set V)))
        = (c2 * c1) * (μ0 (L : Set V) * μ0 (ann χ (L : Set V))) := by ring
      _ = _ := by rw [h12, one_mul]
  exact selfDual_of_pairs χ hχc hχ hsym hn M hMc hMo hNc hNo hex hsh μ0
    (fun k => (hgen k).trans (hgen 0).symm)

theorem exists_selfDual_measure (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
    (hψn : ∀ r, ‖ψ0 r‖ = 1) (hnt : ∃ y, ψ0 y ≠ 1)
    (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBjc : Continuous (fun p : V × V => B p.1 p.2)) (hD : DualAt v B) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ0 (B x y)) := by
  obtain ⟨π, hπ0, hπt, -⟩ := PI.VolStabSW.exists_unif_Fv v
  set χ : V → V → ℂ := fun x y => ψ0 (B x y) with hχdef
  have hχc : Continuous (fun p : V × V => χ p.1 p.2) :=
    hψc.comp hBjc
  have hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y := fun x t y => by
    simp only [hχdef]; rw [hBa, hψa]
  have hsym : ∀ x y, χ x y = χ y x := fun x y => by simp only [hχdef]; rw [hBsym]
  have hn : ∀ x y, ‖χ x y‖ = 1 := fun x y => hψn _
  obtain ⟨L, hLc, hLo, hsL, hK⟩ := hD
  have hBzr : ∀ x, B x 0 = 0 := fun x => by rw [hBsym]; exact B_zero_left v B hBs x
  have hQ : ∀ᶠ q in 𝓝 (0 : V), ∀ x ∈ (L : Set V), B x q ∈ Aset v ψ0 := by
    have hP : ∀ x ∈ (L : Set V), ∀ᶠ z : V × V in 𝓝 ((0 : V), x), B z.2 z.1 ∈ Aset v ψ0 :=
      fun x _ => by
        have hc : Continuous fun z : V × V => B z.2 z.1 :=
          hBjc.comp (continuous_snd.prodMk continuous_fst)
        exact (hc.tendsto ((0 : V), x)).eventually_mem
          (by rw [show B ((0 : V), x).2 ((0 : V), x).1 = 0 from hBzr x]
              exact Aset_mem_nhds v ψ0 hψc hψa hψn)
    exact hLc.eventually_forall_of_forall_eventually (P := fun q x => B x q ∈ Aset v ψ0) hP
  have hNo0 : IsOpen (ann χ (L : Set V)) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
      have := (continuous_sub_right y).tendsto y
      rwa [sub_self] at this
    filter_upwards [ht hQ] with y' hy'
    intro x hx
    have hq : ψ0 (B x (y' - y)) = 1 := by
      have := hy' x hx 1 (one_mem _)
      rwa [one_mul] at this
    have hyx := hy x hx
    show ψ0 (B x y') = 1
    have e1 : y' = y + (y' - y) := by abel
    rw [e1, hBsym, hBa, hψa, hBsym y, hBsym (y' - y)]
    rw [show ψ0 (B x y) = 1 from hyx, hq, one_mul]
  have hNcl : IsClosed (ann χ (L : Set V)) := isClosed_ann χ hχc L
  have hNc0 : IsCompact (ann χ (L : Set V)) := by
    obtain ⟨y0, hy0⟩ := hnt
    obtain ⟨K, hKc, hKs⟩ := hK y0
    refine hKc.of_isClosed_subset hNcl fun y hy => hKs fun x hx => ?_
    apply mem_of_psi v ψ0 y0 _ hy0
    intro s hs'
    obtain ⟨x', hx', hB'⟩ := hsL s hs' x hx
    rw [← hB' y]
    exact hy x' hx'

  set M : ℕ → AddSubgroup V := fun k => L.comap (DistribMulAction.toAddMonoidHom V (π ^ k))
    with hMdef
  have hMset : ∀ k, (M k : Set V) = (fun x => π ^ k • x) ⁻¹' (L : Set V) := fun k => rfl
  have hπk : ∀ k, π ^ k ≠ 0 := fun k => pow_ne_zero k hπ0
  have hann : ∀ k, ann χ (M k : Set V) = (fun y => (π ^ k)⁻¹ • y) ⁻¹' ann χ (L : Set V) := by
    intro k
    ext y
    constructor
    · intro hy x hx
      have hx' : (π ^ k)⁻¹ • x ∈ (M k : Set V) := by
        show π ^ k • ((π ^ k)⁻¹ • x) ∈ L
        rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul]
      have := hy _ hx'
      simp only [hχdef] at this ⊢
      rwa [hBs, hBsym, ← hBs, hBsym] at this
    · intro hy x hx
      have := hy _ hx
      change ψ0 (B (π ^ k • x) ((π ^ k)⁻¹ • y)) = 1 at this
      simp only [hχdef]
      rwa [hBs, hBsym, hBs, hBsym, ← mul_assoc, mul_inv_cancel₀ (hπk k), one_mul] at this
  have hMo : ∀ k, IsOpen (M k : Set V) := fun k => by
    rw [hMset]; exact hLo.preimage (continuous_const_smul _)
  have hMc : ∀ k, IsCompact (M k : Set V) := fun k => by
    rw [hMset]
    exact (Homeomorph.smulOfNeZero (π ^ k) (hπk k)).isCompact_preimage.2 hLc
  have hNo : ∀ k, IsOpen (ann χ (M k : Set V)) := fun k => by
    rw [hann]; exact hNo0.preimage (continuous_const_smul _)
  have hNc : ∀ k, IsCompact (ann χ (M k : Set V)) := fun k => by
    rw [hann]
    exact (Homeomorph.smulOfNeZero ((π ^ k)⁻¹) (inv_ne_zero (hπk k))).isCompact_preimage.2 hNc0
  have hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k := by
    intro y
    have ht : Tendsto (fun k => π ^ k • y) atTop (𝓝 0) := by simpa using hπt.smul_const y
    exact (ht.eventually_mem (hLo.mem_nhds L.zero_mem)).mono fun k hk => hk
  have hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k : Set V) ⊆ U := by
    intro U hU
    have hP : ∀ w ∈ ann χ (L : Set V), ∀ᶠ z : Fv F v × V in 𝓝 ((0 : Fv F v), w), z.1 • z.2 ∈ U :=
      fun w _ => (continuous_smul.tendsto ((0 : Fv F v), w)).eventually_mem
        (by rw [show ((0 : Fv F v), w).1 • ((0 : Fv F v), w).2 = (0 : V) by simp]; exact hU)
    have hev := hNc0.eventually_forall_of_forall_eventually (P := fun c w => c • w ∈ U) hP
    filter_upwards [hπt.eventually hev] with k hk y hy
    rw [hann] at hy
    have := hk _ hy
    rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul] at this

  let μ0 : Measure V := Measure.addHaar
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hNm : MeasurableSet (ann χ (L : Set V)) := hNcl.measurableSet
  have hL0 : μ0 (L : Set V) ≠ 0 := (hLo.measure_pos μ0 ⟨0, L.zero_mem⟩).ne'
  have hLt : μ0 (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hgen : ∀ k, μ0 (M k : Set V) * μ0 (ann χ (M k : Set V)) =
      μ0 (L : Set V) * μ0 (ann χ (L : Set V)) := by
    intro k
    obtain ⟨c1, hc1⟩ := haar_smul_preimage v μ0 (π ^ k) (hπk k)
    obtain ⟨c2, hc2⟩ := haar_smul_preimage v μ0 ((π ^ k)⁻¹) (inv_ne_zero (hπk k))
    have hid : (fun y : V => (π ^ k)⁻¹ • y) ⁻¹' ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) =
        (L : Set V) := by
      ext y; simp [smul_smul, mul_inv_cancel₀ (hπk k)]
    have hm1 : MeasurableSet ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) :=
      hLm.preimage (continuous_const_smul _).measurable
    have h12 : c2 * c1 = 1 := by
      have := hc2 _ hm1
      rw [hid, hc1 _ hLm, ← mul_assoc] at this
      have h3 : μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ = 1 := ENNReal.mul_inv_cancel hL0 hLt
      calc c2 * c1 = c2 * c1 * μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ := by
            rw [mul_assoc (c2 * c1), h3, mul_one]
        _ = 1 := by rw [← this, h3]
    rw [hann, hMset, hc1 _ hLm, hc2 _ hNm]
    calc c1 * μ0 (L : Set V) * (c2 * μ0 (ann χ (L : Set V)))
        = (c2 * c1) * (μ0 (L : Set V) * μ0 (ann χ (L : Set V))) := by ring
      _ = _ := by rw [h12, one_mul]
  exact selfDual_of_pairs χ hχc hχ hsym hn M hMc hMo hNc hNo hex hsh μ0
    (fun k => (hgen k).trans (hgen 0).symm)

end Abs

theorem absolute_self_dual_measure : PI.OmFibreUniq.W.Sd.AbsSd := by
  intro F _ _ v ψ0 hψc hψa hψn hnt V _ _ _ _ _ _ _ _ _ _ B hBa hBs hBsym hBc ι _ β β' h1 h2
  exact absSd_main v B ψ0 hψc hψa hψn hnt hBa hBs hBsym hBc β β' h1 h2

end PI.OmFibreUniq.W.SdAbs
