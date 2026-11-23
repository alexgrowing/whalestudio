import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHF

noncomputable section

namespace PI.VolStabSW

namespace FibGenW

open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Core

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

private theorem isFibreFamily_restrict_of_eqOn_open (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y)
    (G G' : V → X) (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (Q : Set V) (hQo : IsOpen Q)
    (hGG' : ∀ x ∈ Q, G' x = G x) :
    IsFibreFamily μ (fun x => ι (G' x)) ι (U ∩ Q) ν B (fun b => (fib b).restrict Q) := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hQm : MeasurableSet Q := hQo.measurableSet
  refine ⟨?_, ?_, ?_⟩
  · intro b
    rw [Measure.restrict_apply' hQm]
    refine measure_mono_null ?_ (h1 b)
    intro x ⟨hx1, hxQ⟩ hx2
    apply hx1
    obtain ⟨hx3, hxU⟩ := hx2
    refine ⟨?_, hxU, hxQ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx3 ⊢
    rw [hGG' x hxQ, ← hfG x]
    exact hx3
  · intro φ hφ
    rw [Set.inter_comm, ← Measure.restrict_restrict hQm, ← lintegral_indicator hQm,
      h2 _ (hφ.indicator hQm)]
    simp only [lintegral_indicator hQm]
  · intro φ hφc hφs hφt
    obtain ⟨hi, hc⟩ := h3 φ hφc hφs (hφt.trans Set.inter_subset_left)
    have hz : ∀ x, x ∉ Q → φ x = 0 := fun x hx => by
      first
        | exact image_eq_zero_of_notMem_tsupport (fun h => hx (hφt h).2)
        | exact image_eq_zero_of_nmem_tsupport (fun h => hx (hφt h).2)
    refine ⟨fun b hb => (hi b hb).restrict, ?_⟩
    have heq : (fun b => ∫ v, φ v ∂(fib b).restrict Q) = fun b => ∫ v, φ v ∂(fib b) :=
      funext fun b => setIntegral_eq_integral_of_forall_compl_eq_zero hz
    rw [heq]
    exact hc

theorem fib_of_ratio_gen (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (Q : Set V) (hNbU : ∀ x ∈ Q, G x ∈ Nb → x ∈ U) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  classical
  have hQm : MeasurableSet Q := hQo.measurableSet
  by_cases hX : ∃ T' : X, T' ≠ T
  · obtain ⟨T', hT'⟩ := hX
    let G' : V → X := Q.piecewise G (fun _ => T')
    have hG'c : Continuous G' := by
      refine hGc.piecewise (fun a ha => ?_) continuous_const
      have hfr : frontier Q = ∅ := IsClopen.frontier_eq ⟨hQcl, hQo⟩
      rw [hfr] at ha
      exact absurd ha (by simp)
    have hGG' : ∀ x ∈ Q, G' x = G x := fun x hx => by simp [G', hx]
    have hNb' : Nb ∩ {T'}ᶜ ∈ 𝓝 T := Filter.inter_mem hNb (isOpen_compl_singleton.mem_nhds hT'.symm)
    have hNbU' : ∀ x, G' x ∈ Nb ∩ {T'}ᶜ → x ∈ U ∩ Q := by
      intro x hx
      by_cases hxQ : x ∈ Q
      · rw [hGG' x hxQ] at hx
        exact ⟨hNbU x hxQ hx.1, hxQ⟩
      · exfalso
        have h' : G' x = T' := by simp [G', hxQ]
        exact hx.2 (by rw [h']; rfl)
    have hratio' : ∀ n, μ.real (Q ∩ G' ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n) := by
      intro n
      have hs : Q ∩ G' ⁻¹' {z | z - T ∈ H n} = Q ∩ G ⁻¹' {z | z - T ∈ H n} := by
        ext x
        constructor
        · rintro ⟨hx, h⟩
          exact ⟨hx, by simpa only [Set.mem_preimage, hGG' x hx] using h⟩
        · rintro ⟨hx, h⟩
          exact ⟨hx, by simpa only [Set.mem_preimage, hGG' x hx] using h⟩
      rw [hs]
      exact hratio n
    have key := fib_of_ratio μ ν (fun x => ι (G' x)) ι hι G' hG'c (fun x => rfl) (U ∩ Q) B
      (fun b => (fib b).restrict Q) (isFibreFamily_restrict_of_eqOn_open μ ν f ι G G' hfG U B fib hfib Q hQo hGG') T hB
      (Nb ∩ {T'}ᶜ) hNb' hNbU' Q hQo hQcl hQc H hHo hHc hHb κ hratio'
    have hI : ∫ x in Q, Q.indicator (1 : V → ℂ) x ∂(fib T) = ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hx])
    rw [← hI]
    exact key
  · push_neg at hX
    have hall : ∀ z : X, z = T := hX
    haveI : Subsingleton X := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have hTN : T ∈ Nb := mem_of_mem_nhds hNb
    have hQU : Q ⊆ U := fun x hx => hNbU x hx (by rw [hall (G x)]; exact hTN)
    obtain ⟨-, h2, -⟩ := hfib
    have hdis := h2 (Q.indicator 1) (measurable_one.indicator hQm)
    simp only [lintegral_indicator_one hQm] at hdis
    rw [Measure.restrict_apply hQm, Set.inter_eq_left.mpr hQU] at hdis
    have hc : (fun b => fib b Q) = fun _ => fib T Q := funext fun b => by rw [hall b]
    rw [hc, lintegral_const] at hdis
    have hr := hratio 0
    have hset : Q ∩ G ⁻¹' {z | z - T ∈ H 0} = Q := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro _
      rw [hall (G x), sub_self]
      exact (H 0).zero_mem
    have hH0 : ((H 0 : AddSubgroup X) : Set X) = Set.univ := Set.eq_univ_of_forall fun z => by
      rw [hall z, ← hall 0]
      exact (H 0).zero_mem
    rw [hset, hH0] at hr
    have hν1 : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν ⟨T, Set.mem_univ _⟩
    have hν2 : ν Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
    have hνpos : ν.real Set.univ ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hν1, hν2⟩
    have hint : ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (((fib T) Q).toReal : ℂ) := by
      rw [show Q.indicator (1 : V → ℂ) = Q.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hQm]
      simp [Measure.real]
    rw [hint]
    congr 1
    have h3 := congrArg ENNReal.toReal hdis
    rw [ENNReal.toReal_mul] at h3
    have h' : ((fib T) Q).toReal * ν.real Set.univ = κ * ν.real Set.univ := by
      rw [← hr]
      exact h3.symm
    exact mul_right_cancel₀ hνpos h'

end Core

end FibGenW

open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes FibGenW

theorem fibLatGen_holds : FibLatGen := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν f ι hι G hGc hfG U B fib hfib T hB
    L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc hHb Q hQL hQcos hQo hQcl Nb hNb hNbU hyp
  have := hμ
  have := hν
  have hLcl : IsClosed (L : Set V) := AddSubgroup.isClosed_of_isOpen _ hLo
  have hScl : ∀ n, IsClosed {z | z - T ∈ H n} := fun n =>
    (AddSubgroup.isClosed_of_isOpen _ (hHo n)).preimage (continuous_id.sub continuous_const)
  set Pn : ℕ → Set V := fun n => Q ∩ G ⁻¹' {z | z - T ∈ H n} with hPndef
  have hPcl : ∀ n, IsClosed (Pn n) := fun n => hQcl.inter ((hScl n).preimage hGc)
  have hPo : ∀ n, IsOpen (Pn n) := fun n =>
    hQo.inter (((hHo n).preimage (continuous_id.sub continuous_const)).preimage hGc)
  have hPc : ∀ n, IsCompact (Pn n) := fun n => hLc.of_isClosed_subset (hPcl n) (inter_subset_left.trans hQL)
  have hν0 : 0 < ν.real (H 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
      (hHc 0).measure_lt_top.ne
  by_cases hne : (Pn 0).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    obtain ⟨D0, hD0, _⟩ := hyp y0 hy0.1 hy0.2
    have hHa : ∀ n, H n ≤ H 0 := by
      intro n
      rw [← hD0, ← hD0]
      exact AddSubgroup.map_mono (hΛa (Nat.zero_le n))
    have hsat : ∀ y ∈ Pn 0, ∀ Z ∈ Λ 0, y + Z ∈ Pn 0 := by
      rintro y ⟨hyL, hyS⟩ Z hZ
      obtain ⟨D, hD, hG⟩ := hyp y hyL hyS
      refine ⟨hQcos y hyL Z hZ, ?_⟩
      have h1 := hG 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero] at h1
      have h2 : D Z ∈ H 0 := hD 0 ▸ AddSubgroup.mem_map_of_mem D hZ
      have hyS' : G y - T ∈ H 0 := hyS
      show G (y + Z) - T ∈ H 0
      have e : G (y + Z) - T = (G (y + Z) - G y - D Z) + D Z + (G y - T) := by abel
      rw [e]
      exact (H 0).add_mem ((H 0).add_mem (hHa 1 h1) h2) hyS'
    have : DiscreteTopology (V ⧸ Λ 0) := QuotientAddGroup.discreteTopology (hΛo 0)
    let q : V → V ⧸ Λ 0 := QuotientAddGroup.mk
    have hq : Continuous q := continuous_quot_mk
    have hfin : (q '' Pn 0).Finite := ((hPc 0).image hq).finite_of_discrete
    set Tf := hfin.toFinset with hTf
    have hmemT : ∀ p, p ∈ Tf ↔ ∃ y ∈ Pn 0, q y = p := by
      intro p
      simp [hTf]
    have hcos : ∀ y, q ⁻¹' {q y} = {x | x - y ∈ Λ 0} := by
      intro y
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]
      exact QuotientAddGroup.eq_iff_sub_mem
    have hcount : ∀ n, μ (Pn n) * ν (H 0) = (Tf.card : ENNReal) * (μ (Λ 0) * ν (H n)) := by
      intro n
      have hdec : Pn n = ⋃ p ∈ Tf, (Pn n ∩ q ⁻¹' {p}) := by
        ext x
        simp only [mem_iUnion, exists_prop]
        constructor
        · intro hx
          refine ⟨q x, (hmemT _).2 ⟨x, ⟨hx.1, hHa n hx.2⟩, rfl⟩, hx, rfl⟩
        · rintro ⟨_, _, hx, _⟩
          exact hx
      have hdisj : PairwiseDisjoint (↑Tf : Set (V ⧸ Λ 0)) (fun p => Pn n ∩ q ⁻¹' {p}) :=
        fun p _ p' _ hne => ((disjoint_singleton.2 hne).preimage q).mono inter_subset_right
          inter_subset_right
      have hmeas : ∀ p ∈ Tf, MeasurableSet (Pn n ∩ q ⁻¹' {p}) := fun p _ =>
        (hPo n).measurableSet.inter
          ((isOpen_discrete ({p} : Set (V ⧸ Λ 0))).preimage hq).measurableSet
      have hval : ∀ p ∈ Tf, μ (Pn n ∩ q ⁻¹' {p}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
        intro p hp
        obtain ⟨y, hy, rfl⟩ := (hmemT p).1 hp
        obtain ⟨D, hD, hG⟩ := hyp y hy.1 hy.2
        have e : Pn n ∩ q ⁻¹' {q y} = {x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n} := by
          rw [hcos]
          ext x
          simp only [hPndef, mem_inter_iff, mem_setOf_eq, mem_preimage]
          constructor
          · rintro ⟨⟨_, hxS⟩, hxy⟩
            exact ⟨hxy, hxS⟩
          · rintro ⟨hxy, hxS⟩
            refine ⟨⟨?_, hxS⟩, hxy⟩
            have := hQcos y hy.1 (x - y) hxy
            rwa [add_sub_cancel] at this
        rw [e]
        exact cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hy.2 n
      conv_lhs => rw [hdec]
      rw [measure_biUnion_finset hdisj hmeas, Finset.sum_mul, Finset.sum_congr rfl hval,
        Finset.sum_const, nsmul_eq_mul]
    have hreal : ∀ n, μ.real (Pn n) * ν.real (H 0) = (Tf.card : ℝ) * (μ.real (Λ 0 : Set V) * ν.real (H n)) := by
      intro n
      have e' := congrArg ENNReal.toReal (hcount n)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← measureReal_def] at e'
      exact e'
    have hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) =
        μ.real (Pn 0) / ν.real (H 0) * ν.real (H n) := by
      intro n
      have h0 := hreal 0
      have hn := hreal n
      show μ.real (Pn n) = _
      have e0 : μ.real (Pn 0) = (Tf.card : ℝ) * μ.real (Λ 0 : Set V) := by
        have h' : μ.real (Pn 0) * ν.real (H 0) =
            ((Tf.card : ℝ) * μ.real (Λ 0 : Set V)) * ν.real (H 0) := by
          rw [h0]
          ring
        exact mul_right_cancel₀ hν0.ne' h'
      rw [e0]
      field_simp
      linarith
    rw [fib_of_ratio_gen μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb _ hNbU hQo hQcl (hLc.of_isClosed_subset hQcl hQL) H hHo hHc
      hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]
  · have hP0 : Pn 0 = ∅ := not_nonempty_iff_eq_empty.1 hne
    have hP0' : Q ∩ G ⁻¹' {z | z - T ∈ H 0} = ∅ := hP0
    rw [hP0', measure_empty, ENNReal.zero_div, ENNReal.toReal_zero, Complex.ofReal_zero]
    have hpre : f ⁻¹' {ι T} = G ⁻¹' {T} := by
      ext x
      simp [hfG, hι.eq_iff]
    have hm : G ⁻¹' {T} ∩ U ∈ ae (fib T) := by
      rw [mem_ae_iff, ← hpre]
      exact hfib.1 T
    have hae : ∀ᵐ x ∂(fib T), Q.indicator (1 : V → ℂ) x = 0 := by
      filter_upwards [hm] with x hx
      have hxT : G x = T := hx.1
      by_cases hxL : x ∈ Q
      · exfalso
        have : x ∈ Pn 0 := ⟨hxL, by
          show G x - T ∈ H 0
          rw [hxT, sub_self]
          exact (H 0).zero_mem⟩
        rw [hP0] at this
        exact this
      · exact indicator_of_notMem hxL _
    rw [integral_congr_ae hae, integral_zero]

end PI.VolStabSW
