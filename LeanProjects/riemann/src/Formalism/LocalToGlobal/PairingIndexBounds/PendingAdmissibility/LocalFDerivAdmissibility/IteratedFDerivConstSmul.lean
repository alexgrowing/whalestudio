import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

theorem iteratedFDeriv_const_smul' {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_const_mul (D : D7) {N N' : ℕ} (s : ℂ) (hs : s ≠ 0) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => s * G z) α = s * TaylorLogMetric.taylor D G α := by
  unfold TaylorLogMetric.taylor
  have h := iteratedFDeriv_const_smul' s hs G (Multiset.card α.toMultiset)
  simp only [smul_eq_mul] at h
  rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (hs0 : s ≠ 0) (t : ℂ) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  unfold TaylorLogMetric.lamC
  by_cases ht : t ∈ TaylorLogMetric.Qbar
  · have hst : s * t ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs ht
    rw [dif_pos hst, dif_pos hs, dif_pos ht, ← map_mul]
    rfl
  · have hst : s * t ∉ TaylorLogMetric.Qbar := by
      intro h
      apply ht
      have : s⁻¹ * (s * t) ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.inv_mem hs) h
      rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at this
    rw [dif_neg hst, dif_neg ht, mul_zero]

theorem pSer_const_mul (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pSer D lam (fun z => s * G z) = MvPowerSeries.C (TaylorLogMetric.lamC lam s) * TaylorLogMetric.pSer D lam G := by
  by_cases hs0 : s = 0
  · subst hs0
    ext α
    rw [MvPowerSeries.coeff_C_mul]
    have h0 : TaylorLogMetric.lamC lam 0 = 0 := by
      unfold TaylorLogMetric.lamC
      rw [dif_pos (TaylorLogMetric.Qbar.zero_mem)]
      exact map_zero lam
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => 0 * G z) α) = _
    simp only [zero_mul]
    rw [h0, zero_mul]
    have : TaylorLogMetric.taylor D (fun _ : TaylorLogMetric.VC D N N' => (0 : ℂ)) α = 0 := by
      unfold TaylorLogMetric.taylor
      simp
    rw [this, h0]
  · ext α
    rw [MvPowerSeries.coeff_C_mul]
    show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * G z) α) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D G α)
    rw [taylor_const_mul D s hs0 G α, lamC_mul lam hs hs0]

theorem linSub_smul_C_mul {σ R : Type} [Fintype σ] [CommRing R] (B : σ → σ → R) (c t : R) (G : MvPowerSeries σ R) :
    Formalism.MainNotions.FormalGroupSystem.linSub B (c • (MvPowerSeries.C t * G)) = MvPowerSeries.C (c * t) * Formalism.MainNotions.FormalGroupSystem.linSub B G := by
  have ha : MvPowerSeries.HasSubst (fun x : σ => ∑ y, MvPowerSeries.C (B x y) * (MvPowerSeries.X y : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by simp
  unfold Formalism.MainNotions.FormalGroupSystem.linSub
  rw [MvPowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_C]

theorem linSub_zpow_pSer (D : D7) {N N' p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (B : (D.what₂.Tau × Fin N' × Fin N) → (D.what₂.Tau × Fin N' × Fin N) → ℂ_[p]) (e : ℤ) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    Formalism.MainNotions.FormalGroupSystem.linSub B (((p : ℂ_[p]) ^ e) • TaylorLogMetric.pSer D lam (fun z => s * G z)) =
      MvPowerSeries.C ((p : ℂ_[p]) ^ e * TaylorLogMetric.lamC lam s) * Formalism.MainNotions.FormalGroupSystem.linSub B (TaylorLogMetric.pSer D lam G) := by
  rw [pSer_const_mul D lam hs, linSub_smul_C_mul]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
