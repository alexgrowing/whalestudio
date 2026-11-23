import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR.AbsInv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in

theorem _root_.GlobalTheory.JR.AbsInv.exists_nhds_invariant {f : V → ℂ}
    (hf : _root_.GlobalTheory.JR.IsTest f) :
    ∃ U ∈ 𝓝 (0 : V), ∀ M : AddSubgroup V, (M : Set V) ⊆ U → ∀ x, ∀ m ∈ M, f (x + m) = f x := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  obtain ⟨hlc, hcs⟩ := hf'
  have hK : IsCompact (tsupport f) := hcs
  have hfin : (f '' tsupport f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.mp hK
    have hloc : IsLocallyConstant (f ∘ ((↑) : tsupport f → V)) :=
      hlc.comp_continuous continuous_subtype_val
    have := hloc.range_finite
    rwa [Set.range_comp, Subtype.range_coe] at this
  have hW : ∀ c : ℂ, ∃ W ∈ 𝓝 (0 : V), c ≠ 0 → {x | f x = c} + W ⊆ {x | f x = c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, univ_mem, fun h => (h hc).elim⟩
    · have hsub : {x | f x = c} ⊆ tsupport f := by
        intro x hx
        apply subset_tsupport f
        rw [Function.mem_support, show f x = c from hx]
        exact hc
      obtain ⟨W, hW0, hWs⟩ := compact_open_separated_add_right
        (hK.of_isClosed_subset (hlc.isClosed_fiber c) hsub) (hlc.isOpen_fiber c) subset_rfl
      exact ⟨W, hW0, fun _ => hWs⟩
  choose W hW0 hWsub using hW
  refine ⟨⋂ c ∈ f '' tsupport f, W c, (biInter_mem hfin).2 fun c _ => hW0 c, ?_⟩
  have key : ∀ x m, m ∈ ⋂ c ∈ f '' tsupport f, W c → f x ≠ 0 → f (x + m) = f x := by
    intro x m hm hx
    have hxK : x ∈ tsupport f := subset_tsupport f (Function.mem_support.2 hx)
    have hmW : m ∈ W (f x) := Set.mem_iInter₂.1 hm (f x) ⟨x, hxK, rfl⟩
    exact hWsub (f x) hx (Set.add_mem_add (show x ∈ {y | f y = f x} from rfl) hmW)
  intro M hM x m hmM
  by_cases hx : f x = 0
  · by_contra hne
    have h1 := key (x + m) (-m) (hM (neg_mem hmM)) (fun h => hne (h.trans hx.symm))
    rw [add_neg_cancel_right] at h1
    exact hne h1.symm
  · exact key x m (hM hmM) hx

variable [MeasurableSpace V] [BorelSpace V]

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in

theorem _root_.GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate (μ : Measure V) [μ.IsAddHaarMeasure] (g : V → ℂ) (m : V) (c : ℂ)
    (hc : c ≠ 1) (h : ∀ x, g (x + m) = c * g x) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = c * ∫ x, g x ∂μ := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + m) ∂μ := (integral_add_right_eq_self g m).symm
      _ = ∫ x, c * g x ∂μ := integral_congr_ae (Eventually.of_forall fun x => h x)
      _ = c * ∫ x, g x ∂μ := integral_const_mul c _
  have h2 : (1 - c) * ∫ x, g x ∂μ = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.2 h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc.symm)

variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in
private theorem fourB_eq_zero_of_not_mem_annihilator (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : V → V → ℂ) (ha : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (M N : AddSubgroup V) (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) (f : V → ℂ)
    (hi : ∀ x, ∀ m ∈ M, f (x + m) = f x) (y : V) (hy : y ∉ N) :
    _root_.GlobalTheory.JR.fourB μ B f y = 0 := by
  have hex : ∃ m ∈ M, B m y ≠ 1 := by
    by_contra h
    push_neg at h
    exact hy ((hN y).2 h)
  obtain ⟨m, hm, hBm⟩ := hex
  unfold _root_.GlobalTheory.JR.fourB
  apply _root_.GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ m (B m y) hBm
  intro x
  rw [hi x m hm, ha]
  ring

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in
private theorem integral_indicator_bicharacter_eq_indicator (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : V → V → ℂ) (hs : ∀ x y, B x y = B y x) (ha : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (M N : AddSubgroup V) (hNo : IsOpen (N : Set V)) (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (w : V) :
    ∫ y, (N : Set V).indicator (fun y => B w y) y ∂μ =
      (M : Set V).indicator (fun _ => ((μ.real N : ℝ) : ℂ)) w := by
  by_cases hw : w ∈ (M : Set V)
  · rw [Set.indicator_of_mem hw]
    have hfun : (N : Set V).indicator (fun y => B w y) = (N : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext y
      by_cases hy : y ∈ (N : Set V)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        exact (hM w).1 hw y hy
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    rw [hfun, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_one]
  · rw [Set.indicator_of_notMem hw]
    have hex : ∃ n ∈ N, B w n ≠ 1 := by
      by_contra h
      push_neg at h
      exact hw ((hM w).2 h)
    obtain ⟨n, hn, hBn⟩ := hex
    apply _root_.GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ n (B w n) hBn
    intro y
    by_cases hy : y ∈ (N : Set V)
    · have hyn : y + n ∈ (N : Set V) := N.add_mem hy hn
      rw [Set.indicator_of_mem hyn, Set.indicator_of_mem hy, hs w (y + n), ha, hs y w, hs n w,
        mul_comm]
    · have hyn : y + n ∉ (N : Set V) := fun h => hy (by simpa using N.sub_mem h hn)
      rw [Set.indicator_of_notMem hyn, Set.indicator_of_notMem hy, mul_zero]

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in

theorem _root_.GlobalTheory.JR.AbsInv.fourB_fourB (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hi : ∀ x, ∀ m ∈ M, f (x + m) = f x) (z : V) :
    _root_.GlobalTheory.JR.fourB μ B (_root_.GlobalTheory.JR.fourB μ B f) z = ((μ.real M * μ.real N : ℝ) : ℂ) * f (-z) := by
  have hNclo : IsClopen (N : Set V) := ⟨N.isClosed_of_isOpen hNo, hNo⟩
  let P : V → V → ℂ := fun x y => (N : Set V).indicator (fun _ => (1 : ℂ)) y * (f x * B x y) * B y z
  have hPy : ∀ y, ∫ x, P x y ∂μ = _root_.GlobalTheory.JR.fourB μ B f y * B y z := by
    intro y
    dsimp only [P]
    rw [integral_mul_const, integral_const_mul]
    congr 1
    by_cases hy : y ∈ (N : Set V)
    · rw [Set.indicator_of_mem hy, one_mul]
      rfl
    · rw [Set.indicator_of_notMem hy, zero_mul,
        fourB_eq_zero_of_not_mem_annihilator μ B ha M N hN f hi y hy]
  have hPx : ∀ x, ∫ y, P x y ∂μ =
      f x * (M : Set V).indicator (fun _ => ((μ.real N : ℝ) : ℂ)) (x + z) := by
    intro x
    rw [← integral_indicator_bicharacter_eq_indicator μ B hs ha M N hNo hM (x + z), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [P]
    by_cases hy : y ∈ (N : Set V)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ha, hs y z]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have hPint : Integrable (Function.uncurry P) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have h1 : Continuous fun q : V × V => (N : Set V).indicator (fun _ => (1 : ℂ)) q.2 :=
        (hNclo.continuous_indicator continuous_const).comp continuous_snd
      have h2 : Continuous fun q : V × V => B q.2 z := hB.comp (continuous_snd.prodMk continuous_const)
      exact (h1.mul ((hf.comp continuous_fst).mul hB)).mul h2
    · apply HasCompactSupport.intro (hfc.isCompact.prod hNc)
      rintro ⟨x, y⟩ hq
      simp only [Set.mem_prod, not_and_or] at hq
      simp only [Function.uncurry_apply_pair, P]
      rcases hq with hx | hy
      · rw [image_eq_zero_of_notMem_tsupport hx]
        ring
      · rw [Set.indicator_of_notMem hy]
        ring
  have hpre : MeasurableSet ((fun x => x + z) ⁻¹' (M : Set V)) :=
    (hMo.preimage (continuous_add_right z)).measurableSet
  calc _root_.GlobalTheory.JR.fourB μ B (_root_.GlobalTheory.JR.fourB μ B f) z
      = ∫ y, _root_.GlobalTheory.JR.fourB μ B f y * B y z ∂μ := rfl
    _ = ∫ y, ∫ x, P x y ∂μ ∂μ := integral_congr_ae (Eventually.of_forall fun y => (hPy y).symm)
    _ = ∫ x, ∫ y, P x y ∂μ ∂μ := (integral_integral_swap hPint).symm
    _ = ∫ x, f x * (M : Set V).indicator (fun _ => ((μ.real N : ℝ) : ℂ)) (x + z) ∂μ :=
        integral_congr_ae (Eventually.of_forall hPx)
    _ = ∫ x, ((fun x => x + z) ⁻¹' (M : Set V)).indicator
          (fun _ => ((μ.real N : ℝ) : ℂ) * f (-z)) x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        by_cases hx : x + z ∈ (M : Set V)
        · have hfx : f x = f (-z) := by
            have e : -z + (x + z) = x := by abel
            have := hi (-z) (x + z) hx
            rwa [e] at this
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => x + z) ⁻¹' (M : Set V) from hx),
            hfx, mul_comm]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (show x ∉ (fun x => x + z) ⁻¹' (M : Set V) from hx), mul_zero]
    _ = ((μ.real M * μ.real N : ℝ) : ℂ) * f (-z) := by
        rw [integral_indicator_const _ hpre, Complex.real_smul]
        simp only [measureReal_def, measure_preimage_add_right]
        push_cast
        ring

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in
private theorem measureReal_mul_eq_of_dual_pairs_subset (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : V → V → ℂ) (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N M' N' : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hMc : IsCompact (M : Set V)) (hNo : IsOpen (N : Set V))
    (hNc : IsCompact (N : Set V)) (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1)
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1) (hM'o : IsOpen (M' : Set V))
    (hN'o : IsOpen (N' : Set V)) (hN'c : IsCompact (N' : Set V))
    (hN' : ∀ y, y ∈ N' ↔ ∀ x ∈ M', B x y = 1) (hM' : ∀ x, x ∈ M' ↔ ∀ y ∈ N', B x y = 1)
    (hle : (M' : Set V) ⊆ M) :
    μ.real M' * μ.real N' = μ.real M * μ.real N := by
  have hMclo : IsClopen (M : Set V) := ⟨M.isClosed_of_isOpen hMo, hMo⟩
  have hf : Continuous ((M : Set V).indicator (fun _ => (1 : ℂ))) :=
    hMclo.continuous_indicator continuous_const
  have hfc : HasCompactSupport ((M : Set V).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)
  have hinv : ∀ L : AddSubgroup V, (L : Set V) ⊆ M → ∀ x, ∀ m ∈ L,
      (M : Set V).indicator (fun _ => (1 : ℂ)) (x + m) = (M : Set V).indicator (fun _ => (1 : ℂ)) x := by
    intro L hL x m hm
    have hmM : m ∈ M := hL hm
    by_cases hx : x ∈ (M : Set V)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (M.add_mem hx hmM)]
    · have hxm : x + m ∉ (M : Set V) := fun h => hx (by simpa using M.sub_mem h hmM)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxm]
  have h1 := _root_.GlobalTheory.JR.AbsInv.fourB_fourB μ B hB hs ha M N hMo hNo hNc hN hM
    _ hf hfc (hinv M subset_rfl) 0
  have h2 := _root_.GlobalTheory.JR.AbsInv.fourB_fourB μ B hB hs ha M' N' hM'o hN'o hN'c
    hN' hM' _ hf hfc (hinv M' hle) 0
  have h0 : (M : Set V).indicator (fun _ => (1 : ℂ)) (-0) = 1 := by
    rw [neg_zero, Set.indicator_of_mem (M.zero_mem)]
  rw [h0, mul_one] at h1 h2
  exact_mod_cast h2.symm.trans h1

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in

theorem _root_.GlobalTheory.JR.AbsInv.exists_selfDual (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (H : ∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧
      IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) ∧
      (∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)) : ∃ μ : Measure V, _root_.GlobalTheory.JR.SelfDual μ B := by
  obtain ⟨M₀, N₀, -, hM₀o, hM₀c, hN₀o, hN₀c, hN₀, hM₀⟩ := H Set.univ univ_mem
  obtain ⟨ν, hν⟩ : ∃ ν : Measure V, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hpos : 0 < ν.real M₀ * ν.real N₀ := by
    apply mul_pos
    · exact ENNReal.toReal_pos (hM₀o.measure_pos ν ⟨0, M₀.zero_mem⟩).ne' hM₀c.measure_lt_top.ne
    · exact ENNReal.toReal_pos (hN₀o.measure_pos ν ⟨0, N₀.zero_mem⟩).ne' hN₀c.measure_lt_top.ne
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (ν.real M₀ * ν.real N₀) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ Real.sqrt_pos.2 hpos
  have hrr : r * r = ν.real M₀ * ν.real N₀ := by
    rw [hr]
    exact Real.mul_self_sqrt hpos.le
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, c = ENNReal.ofReal r⁻¹ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hr0
  have hct : c ≠ ⊤ := hc ▸ ENNReal.ofReal_ne_top
  haveI : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul ν hc0 hct
  have hreal : ∀ A : Set V, (c • ν).real A = r⁻¹ * ν.real A := by
    intro A
    rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hc,
      ENNReal.toReal_ofReal (inv_nonneg.2 hr0.le), measureReal_def]
  have hone : (c • ν).real M₀ * (c • ν).real N₀ = 1 := by
    rw [hreal, hreal]
    calc r⁻¹ * ν.real M₀ * (r⁻¹ * ν.real N₀) = (ν.real M₀ * ν.real N₀) / (r * r) := by ring
      _ = 1 := by rw [hrr, div_self hpos.ne']
  refine ⟨c • ν, ?_⟩
  unfold _root_.GlobalTheory.JR.SelfDual
  refine ⟨inferInstance, ?_⟩
  intro f hf y
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  obtain ⟨U, hU, hUinv⟩ := _root_.GlobalTheory.JR.AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, hMo, hMc, hNo, hNc, hN, hM⟩ :=
    H (U ∩ M₀) (inter_mem hU (hM₀o.mem_nhds M₀.zero_mem))
  have hMN : (c • ν).real M * (c • ν).real N = 1 :=
    (measureReal_mul_eq_of_dual_pairs_subset (c • ν) B hB hs ha M₀ N₀ M N hM₀o hM₀c hN₀o hN₀c
      hN₀ hM₀ hMo hNo hNc hN hM (fun x hx => (hMU hx).2)).trans hone
  rw [_root_.GlobalTheory.JR.AbsInv.fourB_fourB (c • ν) B hB hs ha M N hMo hNo hNc hN hM
    f hf'.1.continuous hf'.2 (hUinv M (fun x hx => (hMU hx).1)) y, hMN]
  simp

end GlobalTheory.JR.AbsInv

open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in

theorem _root_.GlobalTheory.JR.exists_selfDual_of_dual_subgroups : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → ℂ), Continuous (fun p : V × V => B p.1 p.2) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ y, B 0 y = 1) → (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)) → ∃ μ : MeasureTheory.Measure V, _root_.GlobalTheory.JR.SelfDual μ B := by
  intro V _ _ _ _ _ _ _ _ B hB hs ha _ H
  exact _root_.GlobalTheory.JR.AbsInv.exists_selfDual B hB hs ha H
