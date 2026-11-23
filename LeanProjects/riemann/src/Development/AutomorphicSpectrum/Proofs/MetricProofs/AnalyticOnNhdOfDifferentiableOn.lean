import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

def sheetProj (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => Ψ (segre (γ t)) i.succ / Ψ (segre (γ t)) 0

def sheetReg (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (V : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0}

def sheetNorm (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (z : (Σ k, J k) → ℂ) :
    ((k : K) → J k) → ℂ :=
  (Ψ (segre z) 0)⁻¹ • segre z

theorem analyticOnNhd_of_differentiableOn {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : DifferentiableOn ℂ γ V) : AnalyticOnNhd ℂ γ V :=
  fun t ht => analyticAt_pi_iff.mpr fun p => osgood n _ _ hV (differentiableOn_pi.mp hγ p) t ht

theorem analyticAt_psi_segre (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (h : AnalyticAt ℂ γ t) :
    AnalyticAt ℂ (fun t' => Ψ (segre (γ t'))) t := by
  classical
  have h1 : AnalyticAt ℂ (fun t' => segre (γ t')) t :=
    analyticAt_pi_iff.mpr fun (i : (k : K) → J k) =>
      Finset.analyticAt_fun_prod _ fun k _ => analyticAt_coord h ⟨k, i k⟩
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp h1

theorem analyticAt_sheetProj (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (h : AnalyticAt ℂ γ t)
    (h0 : Ψ (segre (γ t)) 0 ≠ 0) : AnalyticAt ℂ (sheetProj Ψ γ) t := by
  have hc := fun j => analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ h) j
  exact analyticAt_pi_iff.mpr fun i => (hc i.succ).div (hc 0) h0

theorem isOpen_sheetReg (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hγ : AnalyticOnNhd ℂ γ V) : IsOpen (sheetReg Ψ γ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨htV, h0, hd⟩
  have hc0 := (analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ (hγ t htV)) 0).continuousAt
  have hcd := (analyticAt_det_fderiv (analyticAt_sheetProj Ψ (hγ t htV) h0)).continuousAt
  filter_upwards [hV.mem_nhds htV, hc0.eventually_ne h0, hcd.eventually_ne hd] with u h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem sheetNorm_mem_fibre {P : Ideal (MRing J)} (hK : Nonempty K) (hP : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ)
    {t : Fin n → ℂ} (hz : γ t ∈ mcPts P) (h0 : Ψ (segre (γ t)) 0 ≠ 0) :
    sheetNorm Ψ (γ t) ∈ fibre P Ψ (sheetProj Ψ γ t) := by
  classical
  obtain ⟨k0⟩ := hK
  set c : K → ℂ := Function.update (fun _ => 1) k0 (Ψ (segre (γ t)) 0)⁻¹ with hc
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [hc, h0]
    · simp [hc, hk]
  have hprod : ∏ k, c k = (Ψ (segre (γ t)) 0)⁻¹ := by
    rw [hc, Finset.prod_update_of_mem (Finset.mem_univ k0)]
    simp
  refine ⟨fun p => c p.1 * γ t p, mcPts_smul hP c hc0 hz, ?_, ?_⟩
  · rw [segre_smul, hprod]; rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [sheetNorm, h0]
    · simp [sheetNorm, sheetProj, div_eq_inv_mul]

theorem sheetNorm_eq_torusSat (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {z z' : (Σ k, J k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h0 : Ψ (segre z) 0 ≠ 0)
    (h0' : Ψ (segre z') 0 ≠ 0) (h : sheetNorm Ψ z = sheetNorm Ψ z') : z ∈ torusSat {z'} := by
  have hs : segre z = (Ψ (segre z) 0 * (Ψ (segre z') 0)⁻¹) • segre z' := by
    have := congrArg (fun v => Ψ (segre z) 0 • v) h
    simpa [sheetNorm, smul_smul, h0] using this
  obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre hz' _ (mul_ne_zero h0 (inv_ne_zero h0')) hs
  exact ⟨z', rfl, c, hc, hcz⟩

theorem sheetProj_fibre_finite {P : Ideal (MRing J)} (hP : IsArithVar P (n + 1))
    {Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {V : Set (Fin n → ℂ)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hmem : ∀ t ∈ V, γ t ∈ mcPts P)
    (hinj : ∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') (y : Fin n → ℂ) :
    ({t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0} ∩ sheetProj Ψ γ ⁻¹' {y}).Finite := by
  refine Set.Finite.of_finite_image (f := fun t => sheetNorm Ψ (γ t))
    ((fibreFinite K J P n Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨t, ⟨⟨htV, h0⟩, hy⟩, rfl⟩
    have := sheetNorm_mem_fibre hP.1 hP.2.1.2.1 Ψ γ (hmem t htV) h0
    rwa [show sheetProj Ψ γ t = y from hy] at this
  · rintro t ⟨⟨ht, h0⟩, -⟩ t' ⟨⟨ht', h0'⟩, -⟩ h
    exact hinj t ht t' ht' (sheetNorm_eq_torusSat Ψ (hmem t' ht').1 h0 h0' h)

theorem sheet_not_flat {P : Ideal (MRing J)} (hP : IsArithVar P (n + 1))
    {Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} (hΨ : IsGoodProj P Ψ)
    {V : Set (Fin n → ℂ)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hV : IsOpen V)
    (hγ : AnalyticOnNhd ℂ γ V) (hmem : ∀ t ∈ V, γ t ∈ mcPts P)
    (hinj : ∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hOV : O ⊆ V) (hne : O.Nonempty) (h0 : ∀ t ∈ O, Ψ (segre (γ t)) 0 ≠ 0)
    (hdet : ∀ t ∈ O, LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO hne
    (fun t ht => analyticAt_sheetProj Ψ (hγ t (hOV ht)) (h0 t ht)) hdet
  exact hy ((sheetProj_fibre_finite hP hΨ hmem hinj y).subset fun t ht =>
    ⟨⟨hOV ht.1, h0 t ht.1⟩, ht.2⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp
