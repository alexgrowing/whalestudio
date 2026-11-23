import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.MatrixCoeffAgree

open scoped ContDiff

variable {n : ℕ} {ε : Fin n → Bool}

theorem exp_mem_UJset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε :=
  GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t

theorem exp_smul_add (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem hasDerivAt_orbit {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} (hσ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {z : E}
    (h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (dRep σ X z) 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (σ (NormedSpace.exp (t • X)) (dRep σ X z)) t := by
  have h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) z) (dRep σ X z) t := by
    have := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h0)
    exact this
  have h2 := ((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [← ContinuousLinearMap.comp_apply, ← hσ.2 _ (exp_mem_UJset hX t) _ (exp_mem_UJset hX (s - t)),
    ← exp_smul_add]
  simp

theorem hasDerivAt_zero_of_smoothVec {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {z : E}
    (hz : Formalism.L2.Theta.SmoothVec (lieSet ε) σ z) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (dRep σ X z) 0 := by
  have h1 := (hz 1 (fun _ => X) (fun _ => hX)).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
  have h2 : ContDiff ℝ ∞ fun s : ℝ => σ (NormedSpace.exp (s • X)) z := by
    simpa [Function.comp_def] using h1
  exact ((h2.differentiable (by simp)) 0).hasDerivAt

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem differentiableAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (t₀ : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => NormedSpace.exp (s • X) a b) t₀ := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) t₀ :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const)
  exact ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).differentiableAt).comp t₀
    h1.differentiableAt

end

theorem hasDerivAt_zero_of_smoothOnH {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {σ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {z : E}
    (hz : Formalism.QuantumDeterminants.SmoothOnH (Jm ε) fun g => σ g z) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) (dRep σ X z) 0 := by
  obtain ⟨U, F, hU, h0, hF, he⟩ := hz 1 (by simp [Formalism.QuantumDeterminants.inUH])
  let U' : Set (Fin n → Fin n → ℂ) := U
  let F' : (Fin n → Fin n → ℂ) → E := F
  have hU' : IsOpen U' := hU
  have hF' : ContDiffOn ℝ ∞ F' U' := hF
  let c : ℝ → (Fin n → Fin n → ℂ) := fun s => Matrix.of.symm (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ)
  have hcd : DifferentiableAt ℝ c 0 :=
    differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => (differentiableAt_exp_entry X a b 0 :)
  have hc0 : c 0 = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [c, zero_smul, NormedSpace.exp_zero]
    rfl
  have hFd : DifferentiableAt ℝ F' (c 0) := by
    rw [hc0]
    exact (hF'.contDiffAt (hU'.mem_nhds h0)).differentiableAt (by simp)
  have hcomp := hFd.comp (0 : ℝ) hcd
  have hev : (fun s : ℝ => σ (NormedSpace.exp (s • X)) z) =ᶠ[nhds 0] F' ∘ c := by
    have : ∀ᶠ s in nhds (0 : ℝ), c s ∈ U' := by
      apply hcd.continuousAt.preimage_mem_nhds
      rw [hc0]
      exact hU'.mem_nhds h0
    filter_upwards [this] with s hs
    exact he _ hs (exp_mem_UJset hX s)
  exact (hcomp.congr_of_eventuallyEq hev).hasDerivAt

theorem eq_zero_of_iteratedDeriv {f : ℝ → ℂ} (hf : ∀ t, AnalyticAt ℝ f t)
    (h : ∀ k : ℕ, iteratedDeriv k f 0 = 0) (t : ℝ) : f t = 0 := by
  obtain ⟨p, r, hp⟩ := hf 0
  have hp0 : p = 0 := by
    ext k y
    have h1 := hp.factorial_smul 1 k
    rw [← iteratedDeriv_eq_iteratedFDeriv, h] at h1
    have h2 : p k (fun _ => 1) = 0 := by
      have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact (smul_eq_zero.1 h1).resolve_left hk
    have h3 : p.coeff k = 0 := h2
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff, h3, smul_zero]
    rfl
  rw [hp0] at hp
  have hev : f =ᶠ[nhds 0] 0 := hp.hasFPowerSeriesAt.eventually_eq_zero
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (U := Set.univ)
    (fun x _ => hf x) isPreconnected_univ (Set.mem_univ 0) hev (Set.mem_univ t)

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  change (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
  simp

theorem coeff_exp_eq (hHC : GlobalTheory.Published.HarishChandraAnalyticity) (hρ : IsAdmRep ε ρ) (hπ : IsAdmRep ε π)
    (hGK : IsGKSub ε ρ (kFinVec ε ρ))
    (hsm : ∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) (T : H →ₗ[ℂ] V)
    (hT : ∀ y, IsKFin ε ρ y → IsKFin ε π (T y))
    (hL : ∀ X ∈ lieSet ε, ∀ y, IsKFin ε ρ y → T (dRep ρ X y) = dRep π X (T y)) {a : H} {w : V}
    (ha : IsKFin ε ρ a) (hw : IsKFin ε π w) (hpair : ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {y : H} (hy : IsKFin ε ρ y) (t : ℝ) :
    ⟪a, ρ (NormedSpace.exp (t • X)) y⟫_ℂ = ⟪w, π (NormedSpace.exp (t • X)) (T y)⟫_ℂ := by
  set G : H → ℝ → ℂ := fun z s =>
    ⟪a, ρ (NormedSpace.exp (s • X)) z⟫_ℂ - ⟪w, π (NormedSpace.exp (s • X)) (T z)⟫_ℂ with hGdef
  have hD : ∀ z, IsKFin ε ρ z → IsKFin ε ρ (dRep ρ X z) := fun z hz =>
    hGK.lieStable X hX z (mem_kFinVec.2 hz)
  have hderiv : ∀ z, IsKFin ε ρ z → ∀ s, HasDerivAt (G z) (G (dRep ρ X z) s) s := by
    intro z hz s
    have h1 := hasDerivAt_orbit hρ.1 hX (hasDerivAt_zero_of_smoothVec hX (hGK.smooth z (mem_kFinVec.2 hz))) s
    have h2 := hasDerivAt_orbit hπ.1 hX (hasDerivAt_zero_of_smoothOnH hX (hsm _ (hT z hz))) s
    have h1' := ((innerSL ℂ a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have h2' := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
    have h3 := h1'.sub h2'
    simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h3
    rw [hGdef]
    simp only
    rw [hL X hX z hz]
    exact h3
  have hiter : ∀ k z, IsKFin ε ρ z → iteratedDeriv k (G z) = G ((dRep ρ X)^[k] z) := by
    intro k
    induction k with
    | zero => intro z _; simp
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ', Function.iterate_succ_apply]
      have : deriv (G z) = G (dRep ρ X z) := funext fun s => (hderiv z hz s).deriv
      rw [this, ih _ (hD z hz)]
  have hkfin : ∀ k, IsKFin ε ρ ((dRep ρ X)^[k] y) := by
    intro k
    induction k with
    | zero => exact hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact hD _ ih
  have hzero : ∀ z, IsKFin ε ρ z → G z 0 = 0 := by
    intro z hz
    simp only [hGdef, zero_smul, NormedSpace.exp_zero, hρ.1.1, hπ.1.1, ContinuousLinearMap.one_apply]
    rw [hpair z hz, sub_self]
  have han : ∀ s, AnalyticAt ℝ (G y) s := by
    intro s
    have h1 := (hHC.1 n ε H ρ hρ y a hy ha).analytic_exp one_mem_UJset hX s
    have h2 := (hHC.1 n ε V π hπ (T y) w (hT y hy) hw).analytic_exp one_mem_UJset hX s
    simp only [Matrix.one_mul] at h1 h2
    exact h1.sub h2
  have := eq_zero_of_iteratedDeriv han (fun k => by rw [hiter k y hy]; exact hzero _ (hkfin k)) t
  exact sub_eq_zero.1 this

end Main

theorem conj_mem_lieSet {k Y : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hY : Y ∈ lieSet ε) :
    k * Y * kᴴ ∈ lieSet ε := by
  have hY' : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
  have hkJ : k * Jm ε = Jm ε * k := hk.2
  have hkJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have := congrArg Matrix.conjTranspose hkJ
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  change (k * Y * kᴴ)ᴴ * Jm ε + Jm ε * (k * Y * kᴴ) = 0
  calc (k * Y * kᴴ)ᴴ * Jm ε + Jm ε * (k * Y * kᴴ)
      = k * (Yᴴ * (kᴴ * Jm ε)) + (Jm ε * k) * Y * kᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = k * (Yᴴ * Jm ε + Jm ε * Y) * kᴴ := by
        rw [hkJ', ← hkJ]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

theorem mul_exp_eq {k Y : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k * NormedSpace.exp Y = NormedSpace.exp ((1 : ℝ) • (k * Y * kᴴ)) * k := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hu : IsUnit k := IsUnit.of_mul_eq_one_right _ h1
  rw [one_smul, ← hinv, Matrix.exp_conj k Y hu, Matrix.mul_assoc _ k⁻¹ k,
    Matrix.nonsing_inv_mul k ((Matrix.isUnit_iff_isUnit_det k).1 hu), Matrix.mul_one]

theorem matrixCoeff_eq : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → IsGKSub ε ρ (kFinVec ε ρ) → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ T : H →ₗ[ℂ] V, (∀ y, IsKFin ε ρ y → IsKFin ε π (T y)) → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ X ∈ lieSet ε, ∀ y, IsKFin ε ρ y → T (dRep ρ X y) = dRep π X (T y)) → ∀ (a : H) (w : V), IsKFin ε ρ a → IsKFin ε π w → (∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) → ∀ y, IsKFin ε ρ y → ∀ g ∈ UJset ε, ⟪a, ρ g y⟫_ℂ = ⟪w, π g (T y)⟫_ℂ := by
  intro hHC n ε H _ _ _ ρ V _ _ _ π hρ hπ hGK hsm T hT hK hL a w ha hw hpair y hy g hg
  obtain ⟨k, hk, Y, hY, rfl⟩ := ReciprocityTheory.ChartRestriction.DS.polar_UJ (show g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε from hg)
  have hk' : k ∈ Kset ε := hk
  have hYl : Y ∈ lieSet ε := hY.1
  have hZ := conj_mem_lieSet hk' hYl
  have hkU := GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk'
  have hky : IsKFin ε ρ (ρ k y) := GlobalTheory.GKModule.isKStableOn_kFinVec ε ρ k hk' y hy
  rw [mul_exp_eq hk', hρ.1.2 _ (exp_mem_UJset hZ 1) _ hkU, hπ.1.2 _ (exp_mem_UJset hZ 1) _ hkU,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hK k hk' y hy]
  exact coeff_exp_eq hHC hρ hπ hGK hsm T hT hL ha hw hpair hZ hky 1

end GlobalTheory.MatrixCoeffAgree

end
