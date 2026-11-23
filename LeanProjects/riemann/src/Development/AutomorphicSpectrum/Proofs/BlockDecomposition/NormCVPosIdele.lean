import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.TorNorm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem norm_cV (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v))) _

theorem cW_posIdele (w : HeightOneSpectrum (𝓞 E)) (ρ : ℝ) (hρ : 0 < ρ) :
    cW w ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E) = 1 :=
  posIdele_finite ρ hρ w

theorem norm_cV_posIdele (v : InfinitePlace E) (ρ : ℝ) (hρ : 0 < ρ) :
    ‖cV v ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E)‖ = ρ := by
  rw [norm_cV]; exact norm_posIdele_infinite ρ hρ v

theorem two_card : 2 * (Fintype.card (InfinitePlace E) : ℝ) = Module.finrank ℚ E := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  push_cast; ring

theorem logAbs_of (u : Ad E) (t : ℝ) (h1 : ∀ v, ‖cV v u‖ = Real.exp t) (h2 : ∀ w, ‖cW w u‖ = 1) :
    logAbs u = Module.finrank ℚ E * t := by
  have : ∀ v : InfinitePlace E, Real.log (‖cV v u‖ ^ 2) = 2 * t := fun v => by
    rw [h1, Real.log_pow, Real.log_exp]; norm_num
  simp only [logAbs, this, h2, Real.log_one, finsum_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_zero]
  rw [← two_card]; ring

theorem tor_neg {n : ℕ} (x : Fin n → ℝ) : (An.tor E x : GA E n)⁻¹ = An.tor E (-x) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  have : ∀ i, posIdele (K := E) (Real.exp ((-x) i)) (Real.exp_pos _) * posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) = 1 := fun i => by
    rw [← posIdeleHom_apply ⟨Real.exp ((-x) i), Real.exp_pos _⟩, ← posIdeleHom_apply ⟨Real.exp (x i), Real.exp_pos _⟩, ← map_mul]
    convert map_one (posIdeleHom E)
    exact Subtype.ext (by simp [← Real.exp_add])
  change diagUnits n _ * diagUnits n _ = 1
  rw [← map_mul]
  convert map_one (diagUnits n (R := Ad E))
  exact funext this

theorem logSizeM_tor {n : ℕ} (x : Fin n → ℝ) :
    logSizeM (An.tor E x : GA E n).val ≤ Module.finrank ℚ E * ‖x‖ := by
  have entry : ∀ i j, (An.tor E x : GA E n).val i j =
      if i = j then ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) else 0 := fun i j => by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val i j = _
    rw [coe_diagUnits, Matrix.diagonal_apply]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have inf : ∀ v : InfinitePlace E,
      Real.posLog (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ 2 * ‖x‖ := fun v => by
    have hle : (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ Real.exp (2 * ‖x‖) := by
      refine Real.iSup_le (fun p => ?_) (Real.exp_pos _).le
      rw [entry]
      split_ifs
      · rw [norm_cV_posIdele, ← Real.exp_nat_mul]
        have : x p.1 ≤ ‖x‖ := (le_abs_self _).trans (norm_le_pi_norm x p.1)
        exact Real.exp_le_exp.2 (by push_cast; linarith)
      · simp [(Real.exp_pos _).le]
    calc _ ≤ Real.posLog (Real.exp (2 * ‖x‖)) :=
          Real.posLog_le_posLog (Real.iSup_nonneg fun _ => by positivity) hle
      _ = 2 * ‖x‖ := by
          rw [Real.posLog, Real.log_exp]
          exact max_eq_right (by positivity)
  have fin : ∀ w : HeightOneSpectrum (𝓞 E),
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w ((An.tor E x : GA E n).val p.1 p.2)‖) = 0 := fun w => by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)]
    refine Real.iSup_le (fun p => ?_) zero_le_one
    rw [entry]
    split_ifs
    · rw [cW_posIdele, norm_one]
    · simp
  unfold logSizeM
  simp only [fin, finsum_zero, add_zero]
  calc _ ≤ ∑ _v : InfinitePlace E, 2 * ‖x‖ := Finset.sum_le_sum fun v _ => inf v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← two_card]; ring

theorem logAbs_det_tor {n : ℕ} (x : Fin n → ℝ) :
    logAbs (An.tor E x : GA E n).val.det = Module.finrank ℚ E * ∑ i, x i := by
  have d : (An.tor E x : GA E n).val.det =
      ∏ i, ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) := by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val.det = _
    rw [coe_diagUnits, det_diagonal]
  rw [d]
  refine logAbs_of _ _ (fun v => ?_) (fun w => ?_)
  · rw [map_prod, norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => norm_cV_posIdele v _ _
  · rw [map_prod, norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [cW_posIdele, norm_one]

theorem torNorm : LogAbsBasic → TorNorm := fun _ E _ _ _ =>
  ⟨fun t => logAbs_of _ t (fun v => norm_cV_posIdele v _ _) (fun w => by rw [cW_posIdele, norm_one]),
    fun n x => ⟨logAbs_det_tor x, by
      have h1 := logSizeM_tor (E := E) x
      have h2 := logSizeM_tor (E := E) (-x)
      rw [norm_neg] at h2
      rw [logSize, tor_neg]
      linarith⟩⟩

end GlobalTheory.CompanionTheory.TorNorm
end
