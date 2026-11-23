import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

namespace PLC

variable {X : Type} [TopologicalSpace X]

theorem fin_one_eq_zero_iff (y : Fin 1 → ℂ) : y = 0 ↔ y 0 = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; funext i; fin_cases i; exact h

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by exact WithTop.coe_le_coe.mpr le_top

open scoped Classical in

def zeroExt (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ)) (v : X → ℝ) (y : Fin 1 → ℂ) : ℝ :=
  if y ∈ ψ.target then v (ψ.symm y) else 0

theorem zeroExt_props [CompactSpace X] [T2Space X] (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ))
    (v : X → ℝ) (hv : ContDiffOn ℝ ∞ (v ∘ ψ.symm) ψ.target) (hvψ : tsupport v ⊆ ψ.source) :
    ContDiff ℝ 2 (zeroExt ψ v) ∧ HasCompactSupport (zeroExt ψ v) ∧
      (∀ y ∈ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] v ∘ ψ.symm) ∧
      (∀ y ∉ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] 0) := by
  have hK : IsCompact (ψ '' tsupport v) :=
    (isClosed_tsupport v).isCompact.image_of_continuousOn (ψ.continuousOn.mono hvψ)
  have hKt : ψ '' tsupport v ⊆ ψ.target := by
    rintro _ ⟨z, hz, rfl⟩; exact ψ.map_source (hvψ hz)
  have hw0 : ∀ y ∉ ψ '' tsupport v, zeroExt ψ v y = 0 := by
    intro y hy
    unfold zeroExt
    split_ifs with ht
    · exact image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, ψ.right_inv ht⟩
    · rfl
  have hloc1 : ∀ y ∈ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] v ∘ ψ.symm := by
    intro y hy
    filter_upwards [ψ.open_target.mem_nhds hy] with y' hy'
    simp [zeroExt, hy']
  have hloc0 : ∀ y ∉ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] 0 := by
    intro y hy
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds (fun h => hy (hKt h))] with y' hy'
    exact hw0 y' hy'
  refine ⟨?_, HasCompactSupport.intro hK hw0, hloc1, hloc0⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ ψ.target
  · exact ((hv.contDiffAt (ψ.open_target.mem_nhds hy)).of_le two_le_inf).congr_of_eventuallyEq
      (hloc1 y hy)
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hloc0 y hy)

theorem plc_local [CompactSpace X] [T2Space X] (A : FinHolAtlas 1 X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (p : Fin r → X)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m (fun k => {p k}))
    (x : X) : ∃ ψ : OpenPartialHomeomorph X (Fin 1 → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
      ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ.source →
        mInt A ![LocPot.ofFun v] (logNormSec L s) = ∑ k, (m k : ℝ) * v (p k) - mInt A ![L] v := by
  classical
  obtain ⟨ψ, hψ, hxψ, hψL, σ, -, hW, u, hu, hu0, hsu⟩ := hsnc x
  refine ⟨ψ, hψ, hxψ, fun v hv hvψ => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ∑ k, if (σ k).isSome then m k else 0 := ⟨_, rfl⟩
  have hs' : ∀ y ∈ ψ.source, s x y = u y * ψ y 0 ^ M := by
    intro y hy
    rw [hsu y hy, hM, ← Finset.prod_pow_eq_pow_sum]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases hk : σ k with _ | i
    · simp
    · obtain rfl := Fin.fin_one_eq_zero i; simp
  have hsum : ∑ k, (m k : ℝ) * v (p k) = (M : ℝ) * zeroExt ψ v 0 := by
    rw [hM, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hWk : ({p k} : Set X) ∩ ψ.source =
        {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0} := hW k
    rcases hk : σ k with _ | i
    · have hp : p k ∉ ψ.source := by
        intro hp
        have h1 : p k ∈ ({p k} ∩ ψ.source : Set X) := ⟨rfl, hp⟩
        rw [hWk] at h1
        obtain ⟨i, hi, -⟩ := h1.2
        rw [hk] at hi; cases hi
      simp [image_eq_zero_of_notMem_tsupport (fun h => hp (hvψ h))]
    · obtain rfl := Fin.fin_one_eq_zero i
      simp only [Option.isSome_some, if_true]
      by_cases hp : p k ∈ ψ.source
      · have h1 : p k ∈ ({p k} ∩ ψ.source : Set X) := ⟨rfl, hp⟩
        rw [hWk] at h1
        obtain ⟨i', -, hi'⟩ := h1.2
        have hψp : ψ (p k) = 0 :=
          (fin_one_eq_zero_iff _).2 (by rwa [Fin.fin_one_eq_zero i'] at hi')
        have h0t : (0 : Fin 1 → ℂ) ∈ ψ.target := hψp ▸ ψ.map_source hp
        have h2 : ψ.symm 0 = p k := by rw [← hψp, ψ.left_inv hp]
        simp [zeroExt, h0t, h2]
      · have hv0 : v (p k) = 0 := image_eq_zero_of_notMem_tsupport fun h => hp (hvψ h)
        have h0t : (0 : Fin 1 → ℂ) ∉ ψ.target := by
          intro h0t
          have hz : ψ.symm 0 ∈ ψ.source := ψ.map_target h0t
          have hz' : ψ.symm 0 ∈ ({y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0} : Set X) :=
            ⟨hz, 0, hk, by rw [ψ.right_inv h0t]; rfl⟩
          rw [← hWk] at hz'
          have h3 : ψ.symm 0 = p k := hz'.1
          exact hp (h3 ▸ hz)
        simp [zeroExt, h0t, hv0]
  obtain ⟨ρ, hρ, hρψ, hρ1⟩ := exists_cutoff A ψ hψ (tsupport v) (isClosed_tsupport v) hvψ
  obtain ⟨B, hAB, j0, hj0⟩ := exists_atlas_with A ψ hψ
  have hvc : Continuous v := continuous_of_smooth A hv
  have hρc : Continuous ρ := continuous_of_smooth A hρ
  obtain ⟨H, hHdef⟩ : ∃ H : X → ℝ, H = fun z => ρ z * (Real.log ‖u z‖ - L.φ x z) := ⟨_, rfl⟩
  have hH : A.Smooth H := by
    intro j
    refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
    by_cases hyψ : (A.chart j).symm y ∈ ψ.source
    · have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target ψ.open_source
      refine ⟨_, hO, ⟨hy.1, hyψ⟩, ?_⟩
      have hS : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∩
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) ⊆
          (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := Set.inter_subset_right
      have h1 := (hρ j).mono (Set.inter_subset_left (t := (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source))
      have hu' : ContDiffOn ℝ ∞ (u ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        ((hu j).contDiffOn hO.uniqueDiffOn).restrict_scalars ℝ
      have h2 : ContDiffOn ℝ ∞ (fun y => Real.log ‖u ((A.chart j).symm y)‖)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        (hu'.norm ℝ fun y hy => hu0 _ hy.2).log fun y hy => norm_ne_zero_iff.2 (hu0 _ hy.2)
      have h3 : ContDiffOn ℝ ∞ (L.φ x ∘ (A.chart j).symm)
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
        (hL.1 x j).mono fun y hy => ⟨hy.1, hψL hy.2⟩
      rw [hHdef]
      exact h1.mul ((h2.mono hS).sub (h3.mono hS))
    · have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport ρ)ᶜ) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
          (isClosed_tsupport ρ).isOpen_compl
      refine ⟨_, hO, ⟨hy.1, fun h => hyψ (hρψ h)⟩, (contDiffOn_const (c := (0 : ℝ))).congr
        fun y' hy' => ?_⟩
      rw [hHdef]
      show ρ _ * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hy'.2.2, zero_mul]
  have hΦv : ∀ i, IsPotential A (![LocPot.ofFun v] i) :=
    Fin.forall_fin_one.2 (isPotential_ofFun A v hv)
  have hΦvB : ∀ i, IsPotential B (![LocPot.ofFun v] i) := fun i =>
    isPotential_of_compatible hAB (hΦv i)
  have hlnsI : MIntegrable A ![LocPot.ofFun v] (logNormSec L s) :=
    logNormIntegrable A L s m (fun k => {p k}) hL hs hsnc _ hΦv
  have hHI : MIntegrable A ![LocPot.ofFun v] H :=
    mIntegrableCont A _ hΦv H (continuous_of_smooth A hH)
  obtain ⟨g, hg⟩ : ∃ g : X → ℝ, g = fun z => logNormSec L s z - H z := ⟨_, rfl⟩
  have hgI : MIntegrable A ![LocPot.ofFun v] g := by
    rw [hg]; exact mIntegrable_sub A _ hlnsI hHI
  have hρgI : MIntegrable A ![LocPot.ofFun v] (fun z => ρ z * g z) :=
    mIntegrableMul A _ g ρ hgI hρc

  have step1 : mInt A ![LocPot.ofFun v] (logNormSec L s) =
      1 * mInt A ![LocPot.ofFun v] g + mInt A ![LocPot.ofFun v] H := by
    rw [← mIntLinear A _ hΦv 1 g H hgI hHI]
    congr 1
    funext z
    rw [hg]
    ring
  have step2a : mInt A ![LocPot.ofFun v] H = mInt A ![LocPot.ofFun H] v :=
    (byPartsSymm (e := 0) A v H hv hH ![] (fun i => i.elim0)).symm
  have hLm : IsPotential A (L.rsmul (-1)) := isPotentialRsmul A (-1) L hL
  have step2b : mInt A ![LocPot.ofFun H] v = mInt A ![L.rsmul (-1)] v := by
    refine mInt_congr A _ _ v v fun j => ae_restrict_of_forall_mem
      (A.chart j).open_target.measurableSet fun y hy => ?_
    by_cases hv0 : v ((A.chart j).symm y) = 0
    · simp [hv0]
    · suffices hd : locDens A ![LocPot.ofFun H] j y = locDens A ![L.rsmul (-1)] j y by rw [hd]
      have hz : (A.chart j).symm y ∈ tsupport v := subset_tsupport _ hv0
      have hzψ : (A.chart j).symm y ∈ ψ.source := hvψ hz
      have hzL : (A.chart j).symm y ∈ L.U x := hψL hzψ
      rw [locDens_ofFun, locDensBase A ![L.rsmul (-1)] (Fin.forall_fin_one.2 hLm) j y hy
        (fun _ => x) (Fin.forall_fin_one.2 hzL)]
      have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {z | v z ≠ 0}) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
          (isOpen_ne_fun hvc continuous_const)
      have hgerm : (H ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun y' =>
          -1 * L.φ x ((A.chart j).symm y') + Real.log ‖(u ∘ (A.chart j).symm) y'‖ := by
        filter_upwards [hO.mem_nhds ⟨hy, hv0⟩] with y' hy'
        rw [hHdef]
        simp only [Function.comp, hρ1 _ (subset_tsupport _ hy'.2)]
        ring
      have hOL : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (L.isOpen_U x)
      have hC2 : ContDiffAt ℝ 2 (fun y' => -1 * L.φ x ((A.chart j).symm y')) y :=
        contDiffAt_const.mul (((hL.1 x j).contDiffAt (hOL.mem_nhds ⟨hy, hzL⟩)).of_le two_le_inf)
      have han : AnalyticAt ℂ (u ∘ (A.chart j).symm) y := hu j y ⟨hy, hzψ⟩
      have key : ReciprocityTheory.AnForm.hessC (H ∘ (A.chart j).symm) y =
          ReciprocityTheory.AnForm.hessC (fun y' => -1 * L.φ x ((A.chart j).symm y')) y := by
        rw [hessCGerm _ _ _ hgerm]
        exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ (u ∘ (A.chart j).symm) y hC2 han (hu0 _ hzψ)
      rw [maDens_one, maDens_one]
      show 2 / Real.pi * (ReciprocityTheory.AnForm.hessC (H ∘ (A.chart j).symm) y 0 0).re =
        2 / Real.pi * (ReciprocityTheory.AnForm.hessC (fun y' => -1 * L.φ x ((A.chart j).symm y')) y 0 0).re
      rw [key]
  have step2c : mInt A ![L.rsmul (-1)] v = -1 * mInt A ![L] v :=
    mIntRsmul (e := 0) A (-1) L ![] hL (fun i => i.elim0) v

  have step3 : mInt A ![LocPot.ofFun v] g = mInt A ![LocPot.ofFun v] (fun z => ρ z * g z) :=
    mInt_ofFun_congr A v _ _ fun z hz => by rw [hρ1 z hz, one_mul]
  have hIB := mIntAtlasIndep A B hAB _ hΦv _ hρgI
  obtain ⟨P⟩ := existsPartition B
  have hsuppB : tsupport (fun z => ρ z * g z) ⊆ (B.chart j0).source := by
    rw [hj0]; exact tsupport_mul_subset_left.trans hρψ
  have step4 : mInt A ![LocPot.ofFun v] (fun z => ρ z * g z) =
      ∫ y in ψ.target, ρ (ψ.symm y) * g (ψ.symm y) * ReciprocityTheory.AnForm.maDens ![v ∘ ψ.symm] y := by
    rw [hIB.2, mIntEq B P _ hΦvB _ hIB.1, mIntLocalize B P _ hΦvB j0 _ hsuppB hIB.1]
    simp only [locDens_ofFun, hj0]
  have hvψs : ContDiffOn ℝ ∞ (v ∘ ψ.symm) ψ.target := by
    have h1 := smoothOn_of_compatible hAB isOpen_univ hv j0
    rw [hj0] at h1
    simpa using h1
  obtain ⟨hw2, hwc, hw1, hw0'⟩ := zeroExt_props ψ v hvψs hvψ
  have step5 : ∫ y in ψ.target, ρ (ψ.symm y) * g (ψ.symm y) *
      ReciprocityTheory.AnForm.maDens ![v ∘ ψ.symm] y = (M : ℝ) * zeroExt ψ v 0 := by
    have hG := ReciprocityTheory.AnForm.A.greenMaDens_thm (zeroExt ψ v) hw2 hwc
    rw [← hG.2, ← integral_const_mul,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ψ.target) (μ := volume)
        (f := fun y => (M : ℝ) * (Real.log ‖y 0‖ * ReciprocityTheory.AnForm.maDens ![zeroExt ψ v] y)) ?_]
    · refine setIntegral_congr_ae ψ.open_target.measurableSet ?_
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Fin 1 → ℂ))] with y hy0 hyt
      have hy0' : y 0 ≠ 0 := fun h => hy0 ((fin_one_eq_zero_iff y).2 h)
      rw [maDens_congr ![zeroExt ψ v] ![v ∘ ψ.symm] y (Fin.forall_fin_one.2 (hw1 y hyt))]
      by_cases hz : ψ.symm y ∈ tsupport v
      · have hzs : ψ.symm y ∈ ψ.source := hvψ hz
        have hψz : ψ (ψ.symm y) = y := ψ.right_inv hyt
        have hψz0 : ψ (ψ.symm y) 0 ≠ 0 := by rw [hψz]; exact hy0'
        have hsne : s x (ψ.symm y) ≠ 0 := by
          rw [hs' _ hzs]; exact mul_ne_zero (hu0 _ hzs) (pow_ne_zero _ hψz0)
        have hln := logNormSecLocal A L s x (ψ.symm y) hs (hψL hzs) hsne
        have hgval : g (ψ.symm y) = (M : ℝ) * Real.log ‖y 0‖ := by
          rw [hg, hHdef]
          beta_reduce
          rw [hρ1 _ hz, hln, hs' _ hzs, hψz, norm_mul, norm_pow,
            Real.log_mul (norm_ne_zero_iff.2 (hu0 _ hzs)) (pow_ne_zero _ (norm_ne_zero_iff.2 hy0')),
            Real.log_pow]
          ring
        rw [hρ1 _ hz, hgval]
        ring
      · rw [maDens_comp_symm_eq_zero ψ v hyt hz]; simp
    · intro y hy
      rw [maDens_one_eq_zero _ y (hw0' y hy)]; simp
  rw [step1, step2a, step2b, step2c, step3, step4, step5, hsum]
  ring

end PLC

end

end ReciprocityTheory.AnForm.M
