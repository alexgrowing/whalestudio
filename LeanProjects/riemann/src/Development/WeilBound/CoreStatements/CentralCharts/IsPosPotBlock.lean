import Development.WeilBound.CoreStatements.CentralCharts.PshAt0
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompatStatement

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

theorem fs_single_h (k₀ : K) (z : (Σ k, J k) → ℂ) :
    (fsHerm J (Pi.single k₀ 1)).h z = Real.sqrt (∑ i, ‖z ⟨k₀, i⟩‖ ^ 2) := by
  show refNorm (Pi.single k₀ 1) z = _
  unfold refNorm
  rw [Finset.prod_eq_single k₀]
  · simp [Real.sqrt_eq_rpow]
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ k₀) h

private theorem fsHerm_unit_h_eq_sqrt_sum_sq {ι : Type} [Fintype ι] (u : (Σ _ : Unit, ι) → ℂ) :
    (fsHerm (fun _ : Unit => ι) fun _ => 1).h u = Real.sqrt (∑ i, ‖u ⟨(), i⟩‖ ^ 2) := by
  rw [fsHerm_h]
  simp [refNorm, Real.sqrt_eq_rpow]

private theorem differentiableAt_div_coord_of_ne_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Q : Type} [Fintype Q]
    {τ : E → Q → ℂ} {y : E} (hτd : DifferentiableAt ℂ τ y) (q₀ : Q) (h0 : τ y q₀ ≠ 0) :
    DifferentiableAt ℂ (fun v q => τ v q / τ v q₀) y := by
  rw [differentiableAt_pi]
  intro q
  have hq : DifferentiableAt ℂ (fun v => τ v q) y := (differentiableAt_pi.1 hτd) q
  have h₀ : DifferentiableAt ℂ (fun v => τ v q₀) y := (differentiableAt_pi.1 hτd) q₀
  simp only [div_eq_mul_inv]
  exact hq.fun_mul (h₀.fun_inv h0)

theorem isPosPot_block (R : AnLogRes P ⊤ n) (k₀ : K)
    (himm : ∀ (x : R.X) (p : J k₀), R.lift x x ⟨k₀, p⟩ ≠ 0 → ∀ j, x ∈ (R.A.chart j).source →
      (fderiv ℂ (fun (v : Fin n → ℂ) (i : J k₀) => R.lift x ((R.A.chart j).symm v) ⟨k₀, i⟩ /
        R.lift x ((R.A.chart j).symm v) ⟨k₀, p⟩) (R.A.chart j x)).ker = ⊥) :
    IsPosPot R.A (potOf R (fsHerm J (Pi.single k₀ 1))) := by
  intro x j y hy w hw
  obtain ⟨hyt, hyU⟩ := hy
  let τ : (Fin n → ℂ) → (Σ _ : Unit, J k₀) → ℂ :=
    fun v q => R.lift x ((R.A.chart j).symm v) ⟨k₀, q.2⟩
  let ψ : ((Σ _ : Unit, J k₀) → ℂ) → ℝ :=
    fun u => Real.log ((fsHerm (fun _ : Unit => J k₀) fun _ => 1).h u)
  have hfun : (potOf R (fsHerm J (Pi.single k₀ 1))).φ x ∘ (R.A.chart j).symm = ψ ∘ τ := by
    funext v
    simp only [Function.comp, potOf, ψ, τ]
    rw [fs_single_h, fsHerm_unit_h_eq_sqrt_sum_sq]
  rw [hfun]
  have hmem := R.mem x _ hyU
  obtain ⟨p, hp⟩ := hmem.1 k₀
  have hτan : AnalyticAt ℂ τ y := by
    rw [analyticAt_pi_iff]
    intro q
    exact R.holo x ⟨k₀, q.2⟩ j y ⟨hyt, hyU⟩
  have hτne : ∀ k : Unit, ∃ i, τ y ⟨k, i⟩ ≠ 0 := fun _ => ⟨p, hp⟩
  have hsm : ContDiffAt ℝ 2 ψ (τ y) :=
    GlobalTheory.CompanionTheory.Ar.PB.PosFs.contDiffAt_log_h (GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _) hτne
  rw [levi_comp w hτan hsm]
  apply GlobalTheory.CompanionTheory.Ar.PB.PosFs.levi_fs_pos hτne
  intro c hc
  apply hw
  set y' := (R.A.chart j).symm y with hy'eq
  have hy'src : y' ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hcy : (R.A.chart j) y' = y := (R.A.chart j).right_inv hyt
  have hUy' : y' ∈ R.U y' := R.mem_U y'
  obtain ⟨c', hc'ne, hc'eq⟩ := R.compat x y' y' ⟨hyU, hUy'⟩
  have hp' : R.lift y' y' ⟨k₀, p⟩ ≠ 0 := by
    intro h
    apply hp
    show R.lift x y' ⟨k₀, p⟩ = 0
    rw [hc'eq]
    simp [h]
  have hker := himm y' p hp' j hy'src
  rw [hcy] at hker
  let ρ : (Fin n → ℂ) → J k₀ → ℂ := fun v i =>
    R.lift x ((R.A.chart j).symm v) ⟨k₀, i⟩ / R.lift x ((R.A.chart j).symm v) ⟨k₀, p⟩
  have hev : (fun (v : Fin n → ℂ) (i : J k₀) => R.lift y' ((R.A.chart j).symm v) ⟨k₀, i⟩ /
      R.lift y' ((R.A.chart j).symm v) ⟨k₀, p⟩) =ᶠ[𝓝 y] ρ := by
    have hcont := (R.A.chart j).continuousAt_symm hyt
    have hnb : (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U y') ∈ 𝓝 y :=
      hcont.preimage_mem_nhds (((R.isOpen_U x).inter (R.isOpen_U y')).mem_nhds ⟨hyU, hUy'⟩)
    filter_upwards [hnb] with v hv
    obtain ⟨d, hdne, hdeq⟩ := R.compat x y' _ hv
    funext i
    simp only [ρ, hdeq]
    rw [mul_div_mul_left _ _ (hdne k₀)]
  have hτd : DifferentiableAt ℂ τ y := hτan.differentiableAt
  let g : (Fin n → ℂ) → (Σ _ : Unit, J k₀) → ℂ := fun v => affCoord (fun _ : Unit => p) (τ v)
  have hg0 : fderiv ℂ g y w = 0 :=
    GlobalTheory.CompanionTheory.Ar.PB.PosFs.fderiv_affCoord_torus (fun _ : Unit => p) hτd (fun _ => hp) hc
  have hgd : DifferentiableAt ℂ g y := differentiableAt_div_coord_of_ne_zero hτd ⟨(), p⟩ hp
  let L : ((Σ _ : Unit, J k₀) → ℂ) →L[ℂ] (J k₀ → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨(), i⟩ : Σ _ : Unit, J k₀)
  have hρ : ρ = L ∘ g := rfl
  have hρ0 : fderiv ℂ ρ y w = 0 := by
    rw [hρ, fderiv_comp y L.differentiableAt hgd, L.fderiv]
    simp [hg0]
  have hmk : w ∈ LinearMap.ker (fderiv ℂ (fun (v : Fin n → ℂ) (i : J k₀) =>
      R.lift y' ((R.A.chart j).symm v) ⟨k₀, i⟩ / R.lift y' ((R.A.chart j).symm v) ⟨k₀, p⟩) y :
        (Fin n → ℂ) →ₗ[ℂ] (J k₀ → ℂ)) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hev.fderiv_eq]
    exact hρ0
  rw [hker] at hmk
  exact (Submodule.mem_bot ℂ).1 hmk

end AnalyticReference.An
