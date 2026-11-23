import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

def tauAt (ha : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (w : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  T0 (expCover a w) + ∑ j, (w (Fin.castLE ha j) / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))

structure IsChart (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)
    (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) : Prop where
  form : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
    L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0
  A_cont : ContinuousOn A (Metric.ball 0 1)
  A_det : (A 0).det ≠ 0
  T_cont : ContinuousOn T0 (Metric.ball 0 1)
  B_psd : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef
  c_pos : 0 < c
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ 1
  im_lower : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : Fin a → ℂ,
    (∀ j, Complex.exp (l j) = z (Fin.castLE L.a_le j)) →
    ((T0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
      Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  sym : ∀ w ∈ logCover L.a_le, (tauAt L.a_le T0 B w)ᵀ = tauAt L.a_le T0 B w
  im_pos : ∀ w ∈ logCover L.a_le, ((tauAt L.a_le T0 B w).map Complex.im).PosDef
  per : ∀ w ∈ logCover L.a_le, ∀ x, L.P w x =
    (A (expCover a w))ᵀ *ᵥ (cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x))

theorem exists_isChart (L : Flat.LogPeriods n a g Λ) : ∃ bas A T0 B c ρ, IsChart L bas A T0 B c ρ := by
  obtain ⟨bas, Q, A, T0, hE, hAd, hA0, hT0, hBpsd, hPa, hPb⟩ := GlobalTheory.T.symplectic_polydisc_period_basis n a g Λ L
  obtain ⟨ρ₁, c, C₁, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousOn A (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hTc : ContinuousOn T0 (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hT0.1 i j).continuousOn
  have hQa : Q.a_le = L.a_le := rfl
  have hτ : ∀ w ∈ logCover L.a_le, Q.τ w = tauAt L.a_le T0 Q.B w := by
    intro w hw
    have h := hT0.2 w hw
    simp only [PeriodPolydisc.tau0] at h
    simp only [tauAt]
    rw [← h]
    exact (sub_add_cancel _ _).symm
  refine ⟨bas, A, T0, Q.B, c, ρ₁, hE, hAc, hA0, hTc, hBpsd, hc, hρ₁, hρ₁1.le, ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    have hz1 : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k)
        (lt_trans (by simpa [dist_zero_right] using hz) hρ₁1)
    let w : Fin n → ℂ := fun k => if h : k.val < a then l ⟨k.val, h⟩ else z k
    have hwj : ∀ j : Fin a, w (Fin.castLE L.a_le j) = l j := by
      intro j
      have hj : (Fin.castLE L.a_le j).val < a := j.2
      simp [w, hj]
    have hexp : expCover a w = z := by
      funext k
      by_cases hk : k.val < a
      · have := hl ⟨k.val, hk⟩
        simp only [expCover, hk, if_true, w, dif_pos]
        rw [this]
        rfl
      · simp [expCover, hk, w]
    have hw : w ∈ logCover L.a_le := by
      refine ⟨fun i => ?_, fun k hk => ?_⟩
      · rw [hwj]
        have h1 : ‖Complex.exp (l i)‖ < 1 := by rw [hl i]; exact hz1 _
        rw [Complex.norm_exp] at h1
        exact Real.exp_lt_one_iff.1 h1
      · have hk' : ¬ k.val < a := not_lt.2 hk
        simp only [w, hk', dif_neg, not_false_eq_true]
        exact hz1 k
    have h1 := (hb w hw (by rw [hexp]; exact Metric.ball_subset_closedBall hz)).1
    rw [hτ w hw] at h1
    simp only [tauAt, hexp, hwj] at h1
    exact h1
  · intro w hw
    rw [← hτ w hw]
    exact Q.symm w hw
  · intro w hw
    rw [← hτ w hw]
    exact Q.im_posDef w hw
  · intro w hw x
    rw [← hτ w hw]
    exact per_coords bas (L.P w) (Q.τ w) (A (expCover a w)) (Q.symm w hw) (hPa w hw) (hPb w hw) x

def chartS (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (x : Λ)
    (z : Fin n → ℂ) : Fin g → ℂ :=
  (A z)ᵀ *ᵥ (cst (uCo bas x) + T0 z *ᵥ cst (vCo bas x))

def chartW (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Submodule ℤ Λ :=
  LinearMap.ker ((∑ j, B j).mulVecLin ∘ₗ vCo bas)

def chartPer (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : chartW bas B →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun x => chartS bas A T0 (x : Λ) 0) (fun x y => by
    simp only [chartS, Submodule.coe_add, map_add, cst_add, mulVec_add]
    abel_nf)

def IsKerProj (S : Matrix (Fin g) (Fin g) ℤ) (Pr : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Pr * Pr = Pr ∧ Prᵀ = Pr ∧ ∀ v : Fin g → ℝ, S.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 ↔ Pr *ᵥ v = v

def compInv (Pr Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℝ :=
  Pr * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr

def chartQ (Pr : Matrix (Fin g) (Fin g) ℝ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (A z)⁻¹ * (compInv Pr ((T0 z).map Complex.im)).map (fun x : ℝ => (x : ℂ)) * ((A z)ᴴ)⁻¹

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
