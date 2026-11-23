import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_unif

section Gen

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_inv [CompactSpace Y] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (π : Y → X)
    (hπ : HoloMap B A π) (hd : IsDegreeOff A B π 1 ∅) (hb : Function.Bijective π) :
    ∃ σ : X → Y, (∀ x, π (σ x) = x) ∧ (∀ y, σ (π y) = y) ∧ HoloMap A B σ ∧
      ∀ x k j, x ∈ (A.chart k).source → σ x ∈ (B.chart j).source →
        Function.Injective (fderiv ℂ (B.chart j ∘ σ ∘ (A.chart k).symm) (A.chart k x)) := by
  obtain ⟨hπc, hπa⟩ := hπ
  obtain ⟨-, -, -, -, -, hdd⟩ := hd
  let Φ : Y ≃ₜ X := (show Continuous (Equiv.ofBijective π hb) from hπc).homeoOfEquivCompactToT2
  let Ψ : Fin A.n → Fin B.n → OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) :=
    fun i j => (B.chart j).symm.trans (Φ.toOpenPartialHomeomorph.trans (A.chart i))
  have key : ∀ i j z, z ∈ (Ψ i j).target →
      AnalyticAt ℂ (Ψ i j).symm z ∧ Function.Injective (fderiv ℂ (Ψ i j).symm z) := by
    intro i j z hz
    have hw : (Ψ i j).symm z ∈ (Ψ i j).source := (Ψ i j).map_target hz
    have han : AnalyticAt ℂ (Ψ i j) ((Ψ i j).symm z) := hπa j i _ ⟨hw.1, hw.2.2⟩
    have hdet : LinearMap.det (fderiv ℂ (Ψ i j) ((Ψ i j).symm z) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 :=
      hdd j i _ hw.1 (by simp) hw.2.2
    let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
      (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv
    have hL : fderiv ℂ (Ψ i j) ((Ψ i j).symm z) = (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :=
      ContinuousLinearMap.ext fun v => rfl
    have hsymm : AnalyticAt ℂ (Ψ i j).symm z := (Ψ i j).analyticAt_symm hz han hL
    have hder : HasFDerivAt (Ψ i j).symm (L.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z :=
      (Ψ i j).hasFDerivAt_symm hz (hL ▸ han.differentiableAt.hasFDerivAt)
    refine ⟨hsymm, ?_⟩
    rw [hder.fderiv]
    exact L.symm.injective
  refine ⟨⇑Φ.symm, fun x => Φ.apply_symm_apply x, fun y => Φ.symm_apply_apply y,
    ⟨Φ.symm.continuous, ?_⟩, ?_⟩
  · intro i j z hz
    exact (key i j z ⟨⟨hz.1, Set.mem_univ _⟩, hz.2⟩).1
  · intro x k j hxk hxj
    have hz : A.chart k x ∈ (Ψ k j).target := by
      refine ⟨⟨(A.chart k).map_source hxk, Set.mem_univ _⟩, ?_⟩
      show Φ.symm ((A.chart k).symm (A.chart k x)) ∈ (B.chart j).source
      rw [(A.chart k).left_inv hxk]
      exact hxj
    exact (key k j _ hz).2

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {W : Set X}
    {f : X → ℂ} (hf : A.HoloOn W f) : B.HoloOn (h ⁻¹' W) (fun y => f (h y)) := by
  intro j z hz
  obtain ⟨hzt, hzW⟩ := hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm z))
  obtain ⟨hhc, hha⟩ := hh
  have hin : AnalyticAt ℂ ((A.chart k) ∘ h ∘ (B.chart j).symm) z := hha j k z ⟨hzt, hk⟩
  have hout : AnalyticAt ℂ (f ∘ (A.chart k).symm) (((A.chart k) ∘ h ∘ (B.chart j).symm) z) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (h ((B.chart j).symm z))) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hzW
  have hev : ∀ᶠ w in 𝓝 z, h ((B.chart j).symm w) ∈ (A.chart k).source := by
    have hc : ContinuousAt (h ∘ (B.chart j).symm) z :=
      hhc.continuousAt.comp ((B.chart j).continuousAt_symm hzt)
    exact hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  refine (hout.comp hin).congr ?_
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hw]

theorem holoOn_mono {A : FinHolAtlas e X} {W W' : Set X} {f : X → ℂ} (h : A.HoloOn W f) (s : W' ⊆ W) :
    A.HoloOn W' f := by
  intro j
  exact (h j).mono (fun z hz => ⟨hz.1, s hz.2⟩)

theorem holoOn_at {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) {x : X} (hx : x ∈ W) {k : Fin A.n}
    (hk : x ∈ (A.chart k).source) : AnalyticAt ℂ (fun w => f ((A.chart k).symm w)) (A.chart k x) := by
  have := h k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hx⟩
  exact this

theorem exists_holoOn_of_germ (A : FinHolAtlas e X) {x : X} {k : Fin A.n} (hk : x ∈ (A.chart k).source)
    {f : X → ℝ} {H : (Fin e → ℂ) → ℂ} (hH : AnalyticAt ℂ H (A.chart k x))
    (hf : ∀ᶠ w in 𝓝 (A.chart k x), f ((A.chart k).symm w) = (H w).re) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, f y = (G y).re := by
  have hev : ∀ᶠ w in 𝓝 (A.chart k x), AnalyticAt ℂ H w ∧ f ((A.chart k).symm w) = (H w).re :=
    hH.eventually_analyticAt.and hf
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp hev
  refine ⟨(A.chart k).source ∩ (A.chart k) ⁻¹' U, (A.chart k).isOpen_inter_preimage hUo, ⟨hk, hxU⟩,
    fun y => H (A.chart k y), ?_, ?_⟩
  · intro j z hz
    obtain ⟨hzt, hzs, hzU⟩ := hz
    have hin : AnalyticAt ℂ ((A.chart k) ∘ (A.chart j).symm) z := A.holo j k z ⟨hzt, hzs⟩
    have hout : AnalyticAt ℂ H (((A.chart k) ∘ (A.chart j).symm) z) := (hU _ hzU).1
    exact hout.comp hin
  · rintro y ⟨hy, hyU⟩
    have := (hU _ hyU).2
    rwa [(A.chart k).left_inv hy] at this

theorem isOpen_ne {A : FinHolAtlas e X} {W : Set X} (hW : IsOpen W) {T : Type} [Finite T] {f : T → X → ℂ}
    (hf : ∀ t, A.HoloOn W (f t)) : IsOpen {y | y ∈ W ∧ ∀ t, f t y ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyW, hy⟩
  obtain ⟨k, hk⟩ := A.cover y
  have hcont : ∀ t, ContinuousAt (f t) y := by
    intro t
    have han : AnalyticAt ℂ (f t ∘ (A.chart k).symm) (A.chart k y) :=
      hf t k (A.chart k y) ⟨(A.chart k).map_source hk, by
        show (A.chart k).symm (A.chart k y) ∈ W
        rw [(A.chart k).left_inv hk]
        exact hyW⟩
    have hc : ContinuousAt ((f t ∘ (A.chart k).symm) ∘ (A.chart k)) y :=
      han.continuousAt.comp ((A.chart k).continuousAt hk)
    refine hc.congr ?_
    filter_upwards [(A.chart k).open_source.mem_nhds hk] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  have hev : ∀ᶠ z in 𝓝 y, ∀ t, f t z ≠ 0 := by
    rw [Filter.eventually_all]
    intro t
    exact (hcont t).eventually_ne (hy t)
  filter_upwards [hW.mem_nhds hyW, hev] with z hz1 hz2
  exact ⟨hz1, hz2⟩

end Gen

section Mat

variable {N j : ℕ}

theorem lower_left_zero {H X D : Matrix (Fin N) (Fin N) ℂ} (hH : IsBlockDiag j H) (hd : H.det ≠ 0)
    (hD : IsBlockDiag j D) (ht : (H⁻¹ * (X * H + D)).BlockTriangular id) (a b : Fin N) (ha : N - j ≤ (a : ℕ))
    (hb : (b : ℕ) < N - j) : X a b = 0 := by
  classical
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  letI : Invertible H := Matrix.invertibleOfIsUnitDet _ hunit
  have h1 : H.BlockTriangular (fun i : Fin N => if (i : ℕ) < N - j then 0 else 1) := by
    intro r s hrs
    apply hH
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j <;> simp [hr, hs] at hrs ⊢
  have h2 : H.BlockTriangular (fun i : Fin N => if (i : ℕ) < N - j then 1 else 0) := by
    intro r s hrs
    apply hH
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j <;> simp [hr, hs] at hrs ⊢
  have g1 := Matrix.blockTriangular_inv_of_blockTriangular h1
  have g2 := Matrix.blockTriangular_inv_of_blockTriangular h2
  have hI : ∀ r s : Fin N, ¬((r : ℕ) < N - j ↔ (s : ℕ) < N - j) → H⁻¹ r s = 0 := by
    intro r s hrs
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j
    · exact absurd (iff_of_true hr hs) hrs
    · exact g2 (by simp [hr, hs])
    · exact g1 (by simp [hr, hs])
    · exact absurd (iff_of_false hr hs) hrs
  have hY : ∀ c d : Fin N, N - j ≤ (c : ℕ) → (d : ℕ) < N - j → (H⁻¹ * X * H) c d = 0 := by
    intro c d hc hdd
    have hT := ht (show d < c from Fin.lt_def.mpr (by omega))
    rw [Matrix.mul_add, Matrix.add_apply, ← Matrix.mul_assoc] at hT
    have hHD : (H⁻¹ * D) c d = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : (m : ℕ) < N - j
      · rw [hI c m (fun hiff => by have := hiff.mpr hm; omega), zero_mul]
      · rw [hD m d (fun hiff => hm (hiff.mpr hdd)), mul_zero]
    rw [hHD, add_zero] at hT
    exact hT
  have hX : X = H * (H⁻¹ * X * H) * H⁻¹ := by
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [hX, Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  by_cases hm : (m : ℕ) < N - j
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _
    by_cases hc : (c : ℕ) < N - j
    · rw [hH a c (fun hiff => by have := hiff.mpr hc; omega), zero_mul]
    · rw [hY c m (by omega) hm, mul_zero]
  · rw [hI m b (fun hiff => hm (hiff.mpr hb)), mul_zero]

theorem eq_zero_of_lower {L D : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (hD : ∀ a b, a ≤ b → D a b = 0)
    (ht : (L⁻¹ * D).BlockTriangular id) : D = 0 := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  have hlow : L.BlockTriangular OrderDual.toDual :=
    fun i j hij => hL2 i j (OrderDual.toDual_lt_toDual.mp hij)
  have hunit : IsUnit L.det := by
    rw [Matrix.det_of_isLowerTriangular L hlow]
    simp [hL1]
  letI : Invertible L := Matrix.invertibleOfIsUnitDet _ hunit
  have hlow' : L⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hlow
  have hM : L⁻¹ * D = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    rcases lt_or_ge b a with hba | hab
    · exact ht hba
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun c _ => ?_)
      rcases lt_or_ge a c with hac | hca
      · rw [hlow' (OrderDual.toDual_lt_toDual.mpr hac), zero_mul]
      · rw [hD c b (hca.trans hab), mul_zero]
  have h2 := congrArg (fun M => L * M) hM
  simpa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit] using h2

theorem fderiv_mul_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : E → Matrix (Fin N) (Fin N) ℂ}
    {w : E} (hP : ∀ a b, DifferentiableAt ℂ (fun u => P u a b) w) (hQ : ∀ a b, DifferentiableAt ℂ (fun u => Q u a b) w)
    (v : E) : (Matrix.of fun a b => fderiv ℂ (fun u => (P u * Q u) a b) w v) =
      (Matrix.of fun a b => fderiv ℂ (fun u => P u a b) w v) * Q w +
        P w * Matrix.of fun a b => fderiv ℂ (fun u => Q u a b) w v := by
  ext a b
  have h1 : HasFDerivAt (fun u => ∑ c, P u a c * Q u c b)
      (∑ c, (P w a c • fderiv ℂ (fun u => Q u c b) w + Q w c b • fderiv ℂ (fun u => P u a c) w)) w :=
    HasFDerivAt.fun_sum fun c _ => (hP a c).hasFDerivAt.fun_mul (hQ c b).hasFDerivAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [h1.fderiv, ← Finset.sum_add_distrib]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

end Mat

end PositivityTheory.Xgp.c_unif
