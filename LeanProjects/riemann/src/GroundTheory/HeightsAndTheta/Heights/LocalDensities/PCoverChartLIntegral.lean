import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsCoverInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm.M MeasureTheory Topology

noncomputable section

namespace CoverChartLIntegral

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isOpen_image_of_cover {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ) (hcov : IsCoveringMap hmaps.restrict)
    (O : Set X) (hO : IsOpen O) (hOM : O ⊆ M₀) : IsOpen (q '' O) := by
  have h1 : IsOpen (hmaps.restrict '' (Subtype.val ⁻¹' O : Set M₀)) :=
    hcov.isOpenMap _ (hO.preimage continuous_subtype_val)
  have h2 := hΔ.isOpen_compl.isOpenMap_subtype_val _ h1
  convert h2 using 1
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hOM hx⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem exists_sheets {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)} {d : ℕ}
    (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : Fin e → ℂ) (hz : z ∉ Δ) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ z ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ ∀ i, Set.BijOn q (W i) U := by
  set f := hmaps.restrict with hf
  set I := f ⁻¹' {(⟨z, hz⟩ : (Δᶜ : Set (Fin e → ℂ)))} with hI
  obtain ⟨hdisc, U', hzU', hU'o, hfU'o, H, hH⟩ := hcov ⟨z, hz⟩
  have himg : Subtype.val '' I = M₀ ∩ q ⁻¹' {z} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.2, ?_⟩
      have hp' : f p = ⟨z, hz⟩ := hp
      show q p = z
      exact congrArg Subtype.val hp'
    · rintro ⟨hx, hqx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hqx, rfl⟩
  have hIe : I.encard = d := by
    rw [← Subtype.val_injective.encard_image, himg, hfib z hz]
  have : Finite I := (Set.finite_of_encard_eq_coe hIe).to_subtype
  have hcard : Nat.card I = d := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hIe]; rfl
  let eI : Fin d ≃ I := ((Finite.equivFin I).trans (finCongr hcard)).symm
  have hqH : ∀ p : f ⁻¹' U', q ((p : M₀) : X) = (H p).1.1.1 := fun p => by
    rw [hH p]; rfl
  let W : Fin d → Set X := fun i =>
    Subtype.val '' (Subtype.val '' {p : f ⁻¹' U' | (H p).2 = eI i} : Set M₀)
  have hmemW : ∀ i x, x ∈ W i ↔ ∃ p : f ⁻¹' U', (H p).2 = eI i ∧ ((p : M₀) : X) = x := by
    intro i x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨Subtype.val '' U', hΔ.isOpen_compl.isOpenMap_subtype_val _ hU'o, ⟨_, hzU', rfl⟩,
    fun u ⟨u', _, hu⟩ => hu ▸ u'.2, W, fun i => ?_, fun i x hx => ?_, fun i k hik => ?_,
    fun x hx hqx => ?_, fun i => ⟨fun x hx => ?_, fun x hx x' hx' hxx => ?_, fun u hu => ?_⟩⟩
  · have hS : IsOpen {p : f ⁻¹' U' | (H p).2 = eI i} :=
      (isOpen_discrete {eI i}).preimage (continuous_snd.comp H.continuous)
    exact hM.isOpenMap_subtype_val _ (hfU'o.isOpenMap_subtype_val _ hS)
  · obtain ⟨p, -, rfl⟩ := (hmemW i x).1 hx
    exact (p : M₀).2
  · refine Set.disjoint_left.2 fun x hx hx' => hik ?_
    obtain ⟨p, hp, rfl⟩ := (hmemW i x).1 hx
    obtain ⟨p', hp', hpp⟩ := (hmemW k _).1 hx'
    have : p' = p := Subtype.val_injective (Subtype.val_injective hpp)
    rw [this, hp] at hp'
    exact eI.injective hp'
  · obtain ⟨u', hu', hu⟩ := hqx
    have hfx : f ⟨x, hx⟩ = u' := Subtype.ext hu.symm
    let p : f ⁻¹' U' := ⟨⟨x, hx⟩, show f ⟨x, hx⟩ ∈ U' by rw [hfx]; exact hu'⟩
    refine ⟨eI.symm (H p).2, (hmemW _ x).2 ⟨p, ?_, rfl⟩⟩
    exact (eI.apply_symm_apply _).symm
  · obtain ⟨p, -, rfl⟩ := (hmemW i x).1 hx
    rw [hqH p]
    exact ⟨(H p).1.1, (H p).1.2, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := (hmemW i x).1 hx
    obtain ⟨p', hp', rfl⟩ := (hmemW i x').1 hx'
    rw [hqH p, hqH p'] at hxx
    have h1 : (H p).1 = (H p').1 := Subtype.val_injective (Subtype.val_injective hxx)
    have h2 : H p = H p' := Prod.ext h1 (hp.trans hp'.symm)
    rw [H.injective h2]
  · obtain ⟨u', hu', rfl⟩ := hu
    let p : f ⁻¹' U' := H.symm (⟨u', hu'⟩, eI i)
    have hHp : H p = (⟨u', hu'⟩, eI i) := H.apply_symm_apply _
    refine ⟨((p : M₀) : X), (hmemW i _).2 ⟨p, by rw [hHp], rfl⟩, ?_⟩
    rw [hqH p, hHp]

theorem exists_section [Nonempty X] {q : X → Fin e → ℂ} {W : Set X} {U : Set (Fin e → ℂ)}
    (hopen : ∀ O : Set X, IsOpen O → O ⊆ W → IsOpen (q '' O)) (hW : IsOpen W)
    (hbij : Set.BijOn q W U) :
    ∃ s : (Fin e → ℂ) → X, ContinuousOn s U ∧ (∀ u ∈ U, s u ∈ W ∧ q (s u) = u) ∧
      ∀ x ∈ W, s (q x) = x := by
  refine ⟨Function.invFunOn q W, ?_, fun u hu => Function.invFunOn_pos (hbij.surjOn hu),
    fun x hx => hbij.injOn.leftInvOn_invFunOn hx⟩
  rw [continuousOn_iff']
  intro t ht
  refine ⟨q '' (W ∩ t), hopen _ (hW.inter ht) Set.inter_subset_left, ?_⟩
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hut, hu⟩
    have h := Function.invFunOn_pos (hbij.surjOn hu)
    exact ⟨⟨_, ⟨h.1, hut⟩, h.2⟩, hu⟩
  · rintro ⟨⟨x, ⟨hxW, hxt⟩, rfl⟩, hu⟩
    refine ⟨?_, hu⟩
    show Function.invFunOn q W (q x) ∈ t
    rw [hbij.injOn.leftInvOn_invFunOn hxW]
    exact hxt

theorem exists_local_data [Nonempty X] {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    {d : ℕ} (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : (Δᶜ : Set (Fin e → ℂ))) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ (z : Fin e → ℂ) ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      ∃ s : Fin d → (Fin e → ℂ) → X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ (∀ i, ContinuousOn (s i) U) ∧
      (∀ i, ∀ u ∈ U, s i u ∈ W i ∧ q (s i u) = u) ∧
      (∀ i, ∀ x ∈ W i, q x ∈ U ∧ s i (q x) = x) := by
  obtain ⟨U, hUo, hzU, hUΔ, W, hWo, hWM, hWd, hWc, hbij⟩ :=
    exists_sheets hM hΔ hmaps hcov hfib z.1 z.2
  have hs := fun i => exists_section
    (fun O hO hOW => isOpen_image_of_cover hΔ hmaps hcov O hO (hOW.trans (hWM i))) (hWo i) (hbij i)
  choose s hsc hsU hsW using hs
  exact ⟨U, hUo, hzU, hUΔ, W, s, hWo, hWM, hWd, hWc, hsc, hsU,
    fun i x hx => ⟨(hbij i).mapsTo hx, hsW i x hx⟩⟩

theorem analyticAt_chart {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) y :=
  analyticAt_pi_iff.2 fun i => hholo i j y hy

theorem measurableSet_piece {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W) (hWM : W ⊆ M₀)
    {B : Set (Fin e → ℂ)} (hB : MeasurableSet B) :
    MeasurableSet (((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩
      (q ∘ (A.chart j).symm) ⁻¹' B) := by
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W with hO
  have hOo : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hWo
  have hc : ContinuousOn (q ∘ (A.chart j).symm) O := fun y hy =>
    (analyticAt_chart j hholo ⟨hy.1, hWM hy.2⟩).continuousAt.continuousWithinAt
  have h1 : MeasurableSet (O.domRestrict (q ∘ (A.chart j).symm) ⁻¹' B) :=
    hc.domRestrict.measurable hB
  have h2 := hOo.measurableSet.subtype_image h1
  rwa [Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe] at h2

theorem piece_eq {A : FinHolAtlas e X} (χ : ChartPartition A) (j : Fin A.n) {q : X → Fin e → ℂ}
    {M₀ : Set X} (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W)
    (hWM : W ⊆ M₀) {U B : Set (Fin e → ℂ)} (hUo : IsOpen U) (hB : MeasurableSet B)
    (hBU : B ⊆ U) {s : (Fin e → ℂ) → X} (hsc : ContinuousOn s U)
    (hsU : ∀ u ∈ U, s u ∈ W ∧ q (s u) = u) (hsW : ∀ x ∈ W, q x ∈ U ∧ s (q x) = x)
    (g : (Fin e → ℂ) → ENNReal) :
    ∫⁻ y in ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩ (q ∘ (A.chart j).symm) ⁻¹' B,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
          ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
      ∫⁻ u in B, ENNReal.ofReal (χ.χ j (s u)) * g u := by
  set φ := A.chart j with hφ
  set D := (φ.target ∩ φ.symm ⁻¹' W) ∩ (q ∘ φ.symm) ⁻¹' B with hD
  have hDm : MeasurableSet D := measurableSet_piece j hholo hWo hWM hB
  have hτ : ∀ y ∈ D, AnalyticAt ℂ (q ∘ φ.symm) y := fun y hy =>
    analyticAt_chart j hholo ⟨hy.1.1, hWM hy.1.2⟩
  have hder : ∀ y ∈ D, HasFDerivWithinAt (q ∘ φ.symm)
      ((fderiv ℂ (q ∘ φ.symm) y).restrictScalars ℝ) D y := fun y hy =>
    ((hτ y hy).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (q ∘ φ.symm) D := by
    intro y hy y' hy' hyy
    have h1 : φ.symm y = φ.symm y' := by
      rw [← (hsW _ hy.1.2).2, ← (hsW _ hy'.1.2).2]
      exact congrArg s hyy
    rw [← φ.right_inv hy.1.1, ← φ.right_inv hy'.1.1, h1]
  set G : (Fin e → ℂ) → ENNReal := fun u => ENNReal.ofReal (χ.χ j (s u)) * g u with hG
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDm hder hinj G
  set T := U ∩ s ⁻¹' φ.source with hT
  have hTo : IsOpen T := hsc.isOpen_inter_preimage hUo φ.open_source
  have himg : (q ∘ φ.symm) '' D = B ∩ T := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hU := hsW _ hy.1.2
      refine ⟨hy.2, hU.1, ?_⟩
      show s (q (φ.symm y)) ∈ φ.source
      rw [hU.2]
      exact φ.map_target hy.1.1
    · rintro ⟨huB, huU, hus⟩
      have hus' : s u ∈ φ.source := hus
      refine ⟨φ (s u), ⟨⟨φ.map_source hus', ?_⟩, ?_⟩, ?_⟩
      · show φ.symm (φ (s u)) ∈ W
        rw [φ.left_inv hus']
        exact (hsU u (hBU huB)).1
      · show q (φ.symm (φ (s u))) ∈ B
        rw [φ.left_inv hus', (hsU u (hBU huB)).2]
        exact huB
      · show q (φ.symm (φ (s u))) = u
        rw [φ.left_inv hus', (hsU u (hBU huB)).2]
  have hrest : ∫⁻ u in B \ T, G u = 0 := by
    rw [setLIntegral_congr_fun (hB.diff hTo.measurableSet) (g := fun _ => 0) ?_, lintegral_zero]
    rintro u ⟨huB, huT⟩
    have hns : s u ∉ φ.source := fun h => huT ⟨hBU huB, h⟩
    have h0 : χ.χ j (s u) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hns (χ.tsupport_subset j h)
    simp only [hG, h0, ENNReal.ofReal_zero, zero_mul]
  have hBT : ∫⁻ u in B, G u = ∫⁻ u in B ∩ T, G u := by
    rw [← lintegral_inter_add_sdiff G B hTo.measurableSet, hrest, add_zero]
  rw [hBT, ← himg, hcv]
  refine setLIntegral_congr_fun hDm fun y hy => ?_
  have hs : s (q (φ.symm y)) = φ.symm y := (hsW _ hy.1.2).2
  simp only [hG, degree_det_restrictScalars, Function.comp_apply]
  rw [hs, abs_of_nonneg (by positivity)]
  ring

theorem proof : CoverChartLIntegral.Statement := by
  intro e X _ _ A χ q M₀ Δ d hyp g hg
  obtain ⟨hM, hholo, hΔ, ⟨hmaps, hcov⟩, hfib⟩ := hyp
  rcases M₀.eq_empty_or_nonempty with hM0 | ⟨x0, hx0⟩
  · have hd : (d : ENNReal) * ∫⁻ z in Δᶜ, g z = 0 := by
      by_cases hne : (Δᶜ : Set (Fin e → ℂ)).Nonempty
      · obtain ⟨z, hz⟩ := hne
        have h := hfib z hz
        rw [hM0, Set.empty_inter, Set.encard_empty] at h
        have hd0 : d = 0 := by exact_mod_cast h.symm
        simp [hd0]
      · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, lintegral_zero_measure,
          mul_zero]
    rw [hd]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hM0, Set.preimage_empty, Set.inter_empty, Measure.restrict_empty, lintegral_zero_measure]
  have : Nonempty X := ⟨x0⟩
  have : Nonempty (Δᶜ : Set (Fin e → ℂ)) := ⟨⟨q x0, hmaps hx0⟩⟩
  choose U hUo hzU hUΔ W s hWo hWM hWd hWc hsc hsU hsW using
    exists_local_data hM hΔ hmaps hcov hfib

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : (Δᶜ : Set (Fin e → ℂ)) => U z) fun z => hUo z
  obtain ⟨c, hc⟩ := Set.countable_iff_exists_subset_range.1 hTc
  set Un : ℕ → Set (Fin e → ℂ) := fun n => U (c n) with hUn
  set B := disjointed Un with hBdef
  have hBm : ∀ n, MeasurableSet (B n) :=
    MeasurableSet.disjointed fun n => (hUo (c n)).measurableSet
  have hBU : ∀ n, B n ⊆ U (c n) := disjointed_subset Un
  have hBd : Pairwise (Function.onFun Disjoint B) := disjoint_disjointed Un
  have hBcov : (⋃ n, B n) = Δᶜ := by
    rw [iUnion_disjointed]
    refine subset_antisymm (Set.iUnion_subset fun n => hUΔ (c n)) fun z hz => ?_
    have hz' : z ∈ ⋃ w, U w := Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩
    rw [← hTU] at hz'
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 hz'
    obtain ⟨n, rfl⟩ := hc hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩

  have hchart : ∀ j : Fin A.n,
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀,
          ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
            ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
              (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
        ∑' p : ℕ × Fin d, ∫⁻ u in B p.1, ENNReal.ofReal (χ.χ j (s (c p.1) p.2 u)) * g u := by
    intro j
    set D : ℕ × Fin d → Set (Fin e → ℂ) := fun p =>
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W (c p.1) p.2) ∩
        (q ∘ (A.chart j).symm) ⁻¹' B p.1 with hD
    have hDu : (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀ = ⋃ p, D p := by
      ext y
      constructor
      · rintro ⟨hyt, hyM⟩
        have hq : q ((A.chart j).symm y) ∈ ⋃ n, B n := by rw [hBcov]; exact hmaps hyM
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hq
        obtain ⟨i, hi⟩ := hWc (c n) _ hyM (hBU n hn)
        exact Set.mem_iUnion.2 ⟨(n, i), ⟨hyt, hi⟩, hn⟩
      · intro hy
        obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hy
        exact ⟨hp.1.1, hWM _ _ hp.1.2⟩
    have hDd : Pairwise (Function.onFun Disjoint D) := by
      rintro ⟨n, i⟩ ⟨n', i'⟩ hne
      refine Set.disjoint_left.2 fun y hy hy' => ?_
      by_cases hn : n = n'
      · subst hn
        have hi : i ≠ i' := fun h => hne (by rw [h])
        exact Set.disjoint_left.1 (hWd (c n) hi) hy.1.2 hy'.1.2
      · exact Set.disjoint_left.1 (hBd hn) hy.2 hy'.2
    rw [hDu, lintegral_iUnion (fun p => measurableSet_piece j hholo (hWo _ _) (hWM _ _) (hBm _))
      hDd]
    refine tsum_congr fun p => ?_
    exact piece_eq χ j hholo (hWo _ _) (hWM _ _) (hUo _) (hBm _) (hBU _) (hsc _ _) (hsU _ _)
      (hsW _ _) g

  have hsum : ∀ p : ℕ × Fin d,
      ∑ j, ∫⁻ u in B p.1, ENNReal.ofReal (χ.χ j (s (c p.1) p.2 u)) * g u = ∫⁻ u in B p.1, g u := by
    intro p
    rw [← lintegral_finsetSum']
    · refine lintegral_congr fun u => ?_
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun j _ => χ.nonneg j _, χ.sum_eq_one,
        ENNReal.ofReal_one, one_mul]
    · intro j _
      have hχc : Continuous (χ.χ j) := PLC.continuous_of_smooth A (χ.smooth j)
      have h1 : AEMeasurable (fun u => χ.χ j (s (c p.1) p.2 u)) (volume.restrict (U (c p.1))) :=
        (hχc.comp_continuousOn (hsc _ _)).aemeasurable (hUo _).measurableSet
      exact ((ENNReal.measurable_ofReal.comp_aemeasurable h1).mono_measure
        (Measure.restrict_mono (hBU _) le_rfl)).mul hg.aemeasurable
  simp_rw [hchart]
  rw [← Summable.tsum_finsetSum fun j _ => ENNReal.summable]
  simp_rw [hsum]
  rw [ENNReal.tsum_prod']
  simp_rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left, ← lintegral_iUnion hBm hBd, hBcov]

end CoverChartLIntegral

end

end GroundTheory.Heights₂.Heights.FourB
