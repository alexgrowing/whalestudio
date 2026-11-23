import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt jacC maDens_comp integral_image_eq_integral_normSq_det_smul
  integrableOn_image_iff_analytic)
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem contDiff_hypInclAt (i : Fin (e + 1)) : ContDiff ℝ ∞ (hypInclAt (n := e) i) := by
  refine contDiff_pi.2 fun j => ?_
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp only [hypInclAt, Fin.insertNth_apply_same]
    exact contDiff_const
  · simp only [hypInclAt, Fin.insertNth_apply_succAbove]
    exact contDiff_pi.1 contDiff_id k

def removeCLM (i : Fin (e + 1)) : (Fin (e + 1) → ℂ) →L[ℂ] (Fin e → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (i.succAbove k)

section Slice

variable {A : FinHolAtlas (e + 1) X} {W : Set X} {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)}
  {i : Fin (e + 1)}

theorem hyp_remove (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) {p : X} (hpW : p ∈ W)
    (hpψ : p ∈ ψ.source) : hypInclAt i (Fin.removeNth i (ψ p)) = ψ p := by
  have h0 : ψ p i = 0 := by
    have hp : p ∈ W ∩ ψ.source := ⟨hpW, hpψ⟩
    rw [hWψ] at hp
    exact hp.2
  have h1 := Fin.insertNth_self_removeNth i (ψ p)
  rw [h0] at h1
  exact h1

theorem symm_hyp_mem (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) {z : Fin e → ℂ}
    (hz : hypInclAt i z ∈ ψ.target) :
    ψ.symm (hypInclAt i z) ∈ W ∧ ψ.symm (hypInclAt i z) ∈ ψ.source ∧
      Fin.removeNth i (ψ (ψ.symm (hypInclAt i z))) = z := by
  have hq : ψ.symm (hypInclAt i z) ∈ ψ.source := ψ.map_target hz
  have hψq : ψ (ψ.symm (hypInclAt i z)) = hypInclAt i z := ψ.right_inv hz
  refine ⟨?_, hq, ?_⟩
  · have hmem : ψ.symm (hypInclAt i z) ∈ {p ∈ ψ.source | ψ p i = 0} := by
      refine ⟨hq, ?_⟩
      rw [hψq]
      simp [hypInclAt]
    rw [← hWψ] at hmem
    exact hmem.1
  · rw [hψq]
    simp [hypInclAt]

end Slice

section SliceMain

variable [T2Space X] [CompactSpace X] {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
  {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}

def sliceMap (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
    (c : OpenPartialHomeomorph W (Fin e → ℂ)) (y : Fin e → ℂ) : Fin e → ℂ :=
  Fin.removeNth i (ψ ((c.symm y : W) : X))

theorem sliceMap_analytic (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val)
    (hψ : IsCompatChart A ψ) (j : Fin B.n) {V : Set X} (hVψ : V ⊆ ψ.source) :
    AnalyticOnNhd ℂ (sliceMap ψ i (B.chart j))
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V)) := by
  intro y hy
  have hp : (((B.chart j).symm y : W) : X) ∈ ψ.source := hVψ hy.2
  obtain ⟨k, hk⟩ := A.cover (((B.chart j).symm y : W) : X)
  have hg1 : AnalyticAt ℂ (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y := hB.2 j k y ⟨hy.1, hk⟩
  have hg2 : AnalyticAt ℂ (ψ ∘ (A.chart k).symm) ((A.chart k ∘ Subtype.val ∘ (B.chart j).symm) y) := by
    refine (hψ k).1 _ ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (((B.chart j).symm y : W) : X)) ∈ ψ.source
    rw [(A.chart k).left_inv hk]
    exact hp
  have hcont : ContinuousAt (Subtype.val ∘ (B.chart j).symm) y :=
    continuous_subtype_val.continuousAt.comp ((B.chart j).continuousAt_symm hy.1)
  have hev : ∀ᶠ y' in 𝓝 y, (Subtype.val ∘ (B.chart j).symm) y' ∈ (A.chart k).source :=
    hcont.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  have heq : (ψ ∘ (A.chart k).symm) ∘ (A.chart k ∘ Subtype.val ∘ (B.chart j).symm) =ᶠ[𝓝 y]
      fun y' => ψ (((B.chart j).symm y' : W) : X) :=
    hev.mono fun y' hy' => by
      simp only [Function.comp_apply] at hy' ⊢
      rw [(A.chart k).left_inv hy']
  have hψa : AnalyticAt ℂ (fun y' => ψ (((B.chart j).symm y' : W) : X)) y := (hg2.comp hg1).congr heq
  exact ((removeCLM i).analyticAt _).comp hψa

theorem sliceMap_injOn (B : FinHolAtlas e W)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (j : Fin B.n) {V : Set X}
    (hVψ : V ⊆ ψ.source) :
    Set.InjOn (sliceMap ψ i (B.chart j))
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V)) := by
  intro y hy y' hy' h
  have key : ∀ v : Fin (e + 1) → ℂ, v i = 0 → Fin.insertNth i (0 : ℂ) (Fin.removeNth i v) = v :=
    fun v hv => by simpa [hv] using Fin.insertNth_self_removeNth i v
  have hmem : ∀ y' ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (Subtype.val ⁻¹' V),
      (((B.chart j).symm y' : W) : X) ∈ ψ.source ∧ ψ (((B.chart j).symm y' : W) : X) i = 0 := by
    intro y' hy'
    have hs : (((B.chart j).symm y' : W) : X) ∈ ψ.source := hVψ hy'.2
    have hw : (((B.chart j).symm y' : W) : X) ∈ W ∩ ψ.source := ⟨((B.chart j).symm y').2, hs⟩
    rw [hWψ] at hw
    exact ⟨hs, hw.2⟩
  obtain ⟨hs, h0⟩ := hmem y hy
  obtain ⟨hs', h0'⟩ := hmem y' hy'
  have e1 : ψ (((B.chart j).symm y : W) : X) = ψ (((B.chart j).symm y' : W) : X) := by
    rw [← key _ h0, ← key _ h0']
    exact congrArg (Fin.insertNth (α := fun _ => ℂ) i 0) h
  have e2 : (B.chart j).symm y = (B.chart j).symm y' := Subtype.ext (ψ.injOn hs hs' e1)
  exact (B.chart j).symm.injOn hy.1 hy'.1 e2

end SliceMain

section SliceInt

variable [T2Space X] [CompactSpace X] {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
  {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}

open Classical in

def extW (W : Set X) (χ : W → ℝ) (p : X) : ℝ := if h : p ∈ W then χ ⟨p, h⟩ else 0

theorem extW_val (χ : W → ℝ) (q : W) : extW W χ (q : X) = χ q := by
  simp [extW, q.2]

def sliceDens (Φ : Fin e → LocPot X) (x : X) (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) : Fin e → (Fin e → ℂ) → ℝ :=
  fun k => ((Φ k).φ x ∘ ψ.symm) ∘ hypInclAt i

def sliceF (W : Set X) (χ : W → ℝ) (v : X → ℝ) (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) (φ : Fin e → (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) : ℝ :=
  extW W χ (ψ.symm (hypInclAt i z)) * v (ψ.symm (hypInclAt i z)) * maDens φ z

theorem slice_chart (B : FinHolAtlas e W) (hB : HoloMap B A Subtype.val) (Φ : Fin e → LocPot X)
    (hΦ : ∀ k, IsPotential A (Φ k)) (hψ : IsCompatChart A ψ)
    (hWψ : W ∩ ψ.source = {p ∈ ψ.source | ψ p i = 0}) (x : X) (hxW : x ∈ W) {V : Set X}
    (hV : IsOpen V) (hVψ : V ⊆ ψ.source) (hVΦ : ∀ k, V ⊆ (Φ k).U x) {v : X → ℝ}
    (hv : A.Smooth v) (hvV : tsupport v ⊆ V) (P : ChartPartition B) (j : Fin B.n) :
    Integrable ((hypInclAt i ⁻¹' ψ.target).indicator
      (sliceF W (P.χ j) v ψ i (sliceDens Φ x ψ i))) ∧
    ∫ y in (B.chart j).target, P.χ j ((B.chart j).symm y) * (v ∘ Subtype.val) ((B.chart j).symm y) *
      locDens B (fun k => (Φ k).pullback Subtype.val continuous_subtype_val) j y =
    ∫ z, (hypInclAt i ⁻¹' ψ.target).indicator (sliceF W (P.χ j) v ψ i (sliceDens Φ x ψ i)) z := by
  set Ψ : Fin e → LocPot W := fun k => (Φ k).pullback Subtype.val continuous_subtype_val
  set F := sliceF W (P.χ j) v ψ i (sliceDens Φ x ψ i)
  set c := B.chart j
  set S := c.target ∩ c.symm ⁻¹' (Subtype.val ⁻¹' V)
  have hS : IsOpen S :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (hV.preimage continuous_subtype_val)
  set τ := sliceMap ψ i c
  have hτ : AnalyticOnNhd ℂ τ S := sliceMap_analytic B hB hψ j hVψ
  have hinj : Set.InjOn τ S := sliceMap_injOn B hWψ j hVψ
  have hΨ : ∀ k, IsPotential B (Ψ k) := fun k => isPotentialPullback A B Subtype.val hB (Φ k) (hΦ k)
  set I := fun y => P.χ j (c.symm y) * (v ∘ Subtype.val) (c.symm y) * locDens B Ψ j y
  have hpt : ∀ y ∈ S, I y = Complex.normSq (jacC τ y).det • F (τ y) := by
    intro y hy
    have hq := hyp_remove hWψ (c.symm y).2 (hVψ hy.2)
    have hsym : ψ.symm (hypInclAt i (τ y)) = ((c.symm y : W) : X) := by
      show ψ.symm (hypInclAt i (Fin.removeNth i (ψ ((c.symm y : W) : X)))) = _
      rw [hq, ψ.left_inv (hVψ hy.2)]
    have hdens : locDens B Ψ j y =
        maDens (sliceDens Φ x ψ i) (τ y) * Complex.normSq (jacC τ y).det := by
      rw [locDensBase B Ψ hΨ j y hy.1 (fun _ => ⟨x, hxW⟩) (fun k => hVΦ k hy.2)]
      rw [← maDens_comp (sliceDens Φ x ψ i) τ y (hτ y hy) ?_]
      · apply maDens_congr_germ
        intro k
        filter_upwards [hS.mem_nhds hy] with y' hy'
        have h1 := hyp_remove hWψ (c.symm y').2 (hVψ hy'.2)
        show (Φ k).φ x ((c.symm y' : W) : X) =
          (Φ k).φ x (ψ.symm (hypInclAt i (Fin.removeNth i (ψ ((c.symm y' : W) : X)))))
        rw [h1, ψ.left_inv (hVψ hy'.2)]
      · intro k
        have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (Φ k).U x) :=
          ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target ((Φ k).isOpen_U x)
        have hc := contDiffOn_compat hψ ((Φ k).isOpen_U x) ((hΦ k).1 x)
        have hmem : hypInclAt i (τ y) ∈ ψ.target ∩ ψ.symm ⁻¹' (Φ k).U x := by
          refine ⟨?_, ?_⟩
          · show hypInclAt i (Fin.removeNth i (ψ ((c.symm y : W) : X))) ∈ ψ.target
            rw [hq]; exact ψ.map_source (hVψ hy.2)
          · show ψ.symm (hypInclAt i (τ y)) ∈ (Φ k).U x
            rw [hsym]; exact hVΦ k hy.2
        have h2 : ContDiffAt ℝ 2 ((Φ k).φ x ∘ ψ.symm) (hypInclAt i (τ y)) :=
          (hc.contDiffAt (hO.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
        exact h2.comp (τ y) ((contDiff_hypInclAt i).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top))
    simp only [I, F, sliceF, Function.comp_apply, hsym, extW_val, hdens, smul_eq_mul]
    ring
  have hT := c.open_target.measurableSet
  have hSm := hS.measurableSet
  have hzero : ∀ y ∈ c.target \ S, I y = 0 := by
    rintro y ⟨hy, hyS⟩
    have hnV : ((c.symm y : W) : X) ∉ V := fun h => hyS ⟨hy, h⟩
    have hv0 : v ((c.symm y : W) : X) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hnV (hvV h))
    simp [I, hv0]
  have himg : MeasurableSet (τ '' S) := hSm.image_of_continuousOn_injOn hτ.continuousOn hinj
  have hind : (hypInclAt i ⁻¹' ψ.target).indicator F = (τ '' S).indicator F := by
    funext z
    by_cases hz : z ∈ τ '' S
    · obtain ⟨y, hy, rfl⟩ := hz
      have ht : τ y ∈ hypInclAt i ⁻¹' ψ.target := by
        show hypInclAt i (Fin.removeNth i (ψ ((c.symm y : W) : X))) ∈ ψ.target
        rw [hyp_remove hWψ (c.symm y).2 (hVψ hy.2)]; exact ψ.map_source (hVψ hy.2)
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem (Set.mem_image_of_mem τ hy)]
    · rw [Set.indicator_of_notMem hz]
      by_cases ht : hypInclAt i z ∈ ψ.target
      · rw [Set.indicator_of_mem (show z ∈ hypInclAt i ⁻¹' ψ.target from ht)]
        obtain ⟨hpW, _, hrem⟩ := symm_hyp_mem hWψ ht
        by_contra hne
        have h1 : extW W (P.χ j) (ψ.symm (hypInclAt i z)) ≠ 0 := by
          intro h; apply hne; simp [F, sliceF, h]
        have h2 : v (ψ.symm (hypInclAt i z)) ≠ 0 := by
          intro h; apply hne; simp [F, sliceF, h]
        have hχ : P.χ j ⟨_, hpW⟩ ≠ 0 := by simpa [extW, hpW] using h1
        have hsrc : (⟨_, hpW⟩ : W) ∈ c.source := P.tsupport_subset j (subset_tsupport _ hχ)
        have hpV : ψ.symm (hypInclAt i z) ∈ V := hvV (subset_tsupport _ h2)
        apply hz
        refine ⟨c ⟨_, hpW⟩, ⟨c.map_source hsrc, ?_⟩, ?_⟩
        · show ((c.symm (c ⟨_, hpW⟩) : W) : X) ∈ V
          rw [c.left_inv hsrc]; exact hpV
        · show Fin.removeNth i (ψ ((c.symm (c ⟨_, hpW⟩) : W) : X)) = z
          rw [c.left_inv hsrc]; exact hrem
      · rw [Set.indicator_of_notMem (show z ∉ hypInclAt i ⁻¹' ψ.target from ht)]
  have hIT : IntegrableOn I c.target := by
    have hcont : Continuous (fun q : W => P.χ j q * v q) :=
      (smooth_continuous (P.smooth j)).mul ((smooth_continuous hv).comp continuous_subtype_val)
    have hmi := mIntegrableCont B Ψ hΨ _ hcont
    have hKc : IsCompact (c '' tsupport (P.χ j)) :=
      (isClosed_tsupport _).isCompact.image_of_continuousOn (c.continuousOn.mono (P.tsupport_subset j))
    have hKs : c '' tsupport (P.χ j) ⊆ c.target := by
      rintro _ ⟨q, hq, rfl⟩; exact c.map_source (P.tsupport_subset j hq)
    refine IntegrableOn.of_forall_sdiff_eq_zero (hmi j _ hKs hKc) hT ?_
    rintro y ⟨hy, hyK⟩
    have : c.symm y ∉ tsupport (P.χ j) := fun h => hyK ⟨c.symm y, h, c.right_inv hy⟩
    show P.χ j (c.symm y) * v ((c.symm y : W) : X) * locDens B Ψ j y = 0
    rw [image_eq_zero_of_notMem_tsupport this]
    ring
  have hIS : IntegrableOn (fun y => Complex.normSq (jacC τ y).det • F (τ y)) S :=
    (hIT.mono_set Set.inter_subset_left).congr_fun hpt hSm
  have hFimg : IntegrableOn F (τ '' S) :=
    (integrableOn_image_iff_analytic τ S hS hτ hinj F).2 hIS
  refine ⟨?_, ?_⟩
  · rw [hind]; exact (integrable_indicator_iff himg).2 hFimg
  · calc ∫ y in c.target, I y = ∫ y in S, I y :=
          setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hT Set.inter_subset_left hzero
      _ = ∫ y in S, Complex.normSq (jacC τ y).det • F (τ y) := setIntegral_congr_fun hSm hpt
      _ = ∫ z in τ '' S, F z := (integral_image_eq_integral_normSq_det_smul τ S hS hτ hinj F).symm
      _ = _ := by rw [hind, integral_indicator himg]

end SliceInt

end

end ReciprocityTheory.AnForm.M.PLAux
