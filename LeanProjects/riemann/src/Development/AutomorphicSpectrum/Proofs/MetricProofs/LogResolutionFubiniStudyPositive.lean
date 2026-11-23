import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLine
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace PosFs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_one_h (y : (Σ k, ι k) → ℂ) :
    (fsHerm ι fun _ => 1).h y = (GroundTheory.Heights₂.Heights.fsMulti ι).h y := by
  rw [fsHerm_h]
  unfold refNorm
  simp only [GroundTheory.Heights₂.Heights.fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
  norm_num

theorem levi_fs_pos {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < levi (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) z w := by
  have h := GlobalTheory.CompanionTheory.Ar.FS.levi_fsMulti_pos hz hw
  have e : (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) =
      fun y => Real.log ((GroundTheory.Heights₂.Heights.fsMulti ι).h y) := by
    funext y
    rw [fsHerm_one_h]
  rw [e]
  exact h

theorem contDiffAt_log_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have hopen : ∀ᶠ y in 𝓝 z, ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h z := hA.contDiffAt hopen
  exact (h1.of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | (rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) by norm_cast]; exact WithTop.coe_le_coe.2 le_top))).log (A.pos z hz).ne'

theorem fderiv_affCoord_torus {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : E → (Σ k, ι k) → ℂ} {y : E} (p : (k : K) → ι k) (hγ : DifferentiableAt ℂ γ y)
    (hp : ∀ k, γ y ⟨k, p k⟩ ≠ 0) {w : E} {c : K → ℂ} (hc : fderiv ℂ γ y w = torusSmul c (γ y)) :
    fderiv ℂ (fun y' => affCoord p (γ y')) y w = 0 := by
  have hd := hγ.hasFDerivAt
  have hq : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => γ y' q)
      ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y)) y := fun q => hasFDerivAt_pi'.1 hd q
  have hu : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => affCoord p (γ y') q)
      ((γ y q) • ((-((γ y ⟨q.1, p q.1⟩) ^ 2)⁻¹) •
          ((ContinuousLinearMap.proj ⟨q.1, p q.1⟩).comp (fderiv ℂ γ y))) +
        ((γ y ⟨q.1, p q.1⟩)⁻¹) • ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y))) y := by
    intro q
    have hinv := (hasDerivAt_inv (hp q.1)).comp_hasFDerivAt y (hq ⟨q.1, p q.1⟩)
    have hm := (hq q).mul hinv
    refine hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    simp [affCoord, div_eq_mul_inv]
  have hall : fderiv ℂ (fun y' => affCoord p (γ y')) y = ContinuousLinearMap.pi _ :=
    (hasFDerivAt_pi.2 hu).fderiv
  rw [hall]
  funext q
  have h1 : fderiv ℂ γ y w q = c q.1 * γ y q := congrFun hc q
  have h2 : fderiv ℂ γ y w ⟨q.1, p q.1⟩ = c q.1 * γ y ⟨q.1, p q.1⟩ := congrFun hc _
  have hr := hp q.1
  simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    h1, h2, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

theorem isPosPot_fs (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) :
    IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  classical
  intro x j y hy w hw
  obtain ⟨hyt, hyU⟩ := hy
  have hx₀ : (R.A.chart j).symm y ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hex₀ : R.A.chart j ((R.A.chart j).symm y) = y := (R.A.chart j).right_inv hyt
  have hxU : (R.A.chart j).symm y ∈ R.U x := hyU
  let γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y')
  have hγ : AnalyticAt ℂ γ y := analyticAt_pi_iff.2 fun q => R.holo x q j y ⟨hyt, hyU⟩
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := (R.mem x _ hxU).1
  have hc2 := contDiffAt_log_h (GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι fun _ => 1) hz
  have heq : levi ((potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart j).symm) y w =
      levi (fun z => Real.log ((fsHerm ι fun _ => 1).h z)) (γ y) (fderiv ℂ γ y w) :=
    levi_comp w hγ hc2
  rw [heq]
  refine levi_fs_pos hz fun c hc => hw ?_
  choose p hp using (R.mem _ _ (R.mem_U ((R.A.chart j).symm y))).1
  have hnot : R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y) ∉ mcPts (⊤ : Ideal (MRing ι)) := by
    intro h
    have := h.2 1 trivial
    simp at this
  have himm := R.immersion _ hnot p hp j hx₀
  rw [hex₀] at himm
  have hev : (fun y' => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) =ᶠ[𝓝 y]
      fun y' => affCoord p (γ y') := by
    have hmem : (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U ((R.A.chart j).symm y)) ∈ 𝓝 y :=
      ((R.A.chart j).continuousAt_symm hyt).preimage_mem_nhds
        (((R.isOpen_U x).inter (R.isOpen_U _)).mem_nhds ⟨hxU, R.mem_U _⟩)
    filter_upwards [hmem] with y' hy'
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨hy'.2, hy'.1⟩
    funext q
    simp only [affCoord, γ]
    rw [h]
    exact mul_div_mul_left _ _ (hc' q.1)
  rw [hev.fderiv_eq] at himm
  have hpγ : ∀ k, γ y ⟨k, p k⟩ ≠ 0 := by
    intro k
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨R.mem_U _, hxU⟩
    have := hp k
    rw [h] at this
    exact right_ne_zero_of_mul this
  have hk := fderiv_affCoord_torus p hγ.differentiableAt hpγ hc
  have hmem : w ∈ (fderiv ℂ (fun y' => affCoord p (γ y')) y).ker := hk
  rw [himm] at hmem
  exact (Submodule.mem_bot _).1 hmem

end PosFs

theorem fs_pos_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) :=
  fun K _ ι _ P D R => ⟨fun _ hA => isPotential_potOf R hA,
    GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι _, PosFs.isPosPot_fs P D R⟩

end GlobalTheory.CompanionTheory.Ar.PB
