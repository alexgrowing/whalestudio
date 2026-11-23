import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.Lemmas

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Analytic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem lem_nrm (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ A : HS L N [⋀^Fin (k + 1)]→L[ℝ] ℝ,
    ‖A‖ ^ 2 ≤ K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      (A fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 := by
  obtain ⟨Ψ, hΨ⟩ := recon (ι := Fin (k + 1)) (Module.finBasis ℝ (HS L N))
  refine ⟨‖Ψ‖ ^ 2, sq_nonneg _, fun A => ?_⟩
  have h1 := Ψ.le_opNorm (fun v => A fun i => Module.finBasis ℝ (HS L N) (v i))
  rw [hΨ] at h1
  calc ‖A‖ ^ 2 ≤ (‖Ψ‖ * ‖fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
          A fun i => Module.finBasis ℝ (HS L N) (v i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖Ψ‖ ^ 2 * ‖fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
          A fun i => Module.finBasis ℝ (HS L N) (v i)‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_sum _) (sq_nonneg _)

theorem lem_meas {k : ℕ} (d : Dom L N) {ω₁ : Form (HS L N) (k + 1)} (h1 : ContinuousOn ω₁ (Pos L N)) :
    AEStronglyMeasurable (fun x => fr ω₁ (ofS L N x)) (d.μ.restrict d.D) := by
  obtain ⟨Ψ, hΨ⟩ := recon (ι := Fin (k + 1)) (Module.finBasis ℝ (HS L N))
  have hc : Continuous fun x => fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
      fr ω₁ (ofS L N x) fun i => Module.finBasis ℝ (HS L N) (v i) :=
    continuous_pi fun v => (fr_comp_cont h1 _).comp ofS_cont
  have := Ψ.continuous.comp_aestronglyMeasurable (hc.aestronglyMeasurable (μ := d.μ.restrict d.D))
  simpa only [hΨ] using this

theorem lem_gap (hGap : SGap) (hC : IsTotallyComplex L) (π : 𝓞 L) (hπ : Prime π)
    (hπ25 : 25 ≤ Ideal.absNorm (Ideal.span {π})) (h3N : 3 ≤ N) (d : Dom L N) (f : Gp L N → ℝ) (hf : Lz d f)
    (r : ℕ) : Lz d ((hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero))^[r] f) ∧
      ∫ x in d.D, ((hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero))^[r] f) (ofS L N x) ^ 2 ∂d.μ ≤
        ((3 / 5 : ℝ) ^ 2) ^ r * ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ := by
  induction r with
  | zero => exact ⟨hf, by simp⟩
  | succ r ih =>
    obtain ⟨h1, h2⟩ := hGap L hC π hπ hπ25 N h3N d _ ih.1
    rw [Function.iterate_succ_apply']
    refine ⟨h1, h2.trans ((mul_le_mul_of_nonneg_left ih.2 (by norm_num)).trans (le_of_eq ?_))⟩
    ring

end Analytic

theorem lem_bound (hGap : SGap) (hLoc : SLoc) (L : Type) [Field L] [NumberField L] (hC : IsTotallyComplex L)
    (π : 𝓞 L) (hπ : Prime π) (hπ25 : 25 ≤ Ideal.absNorm (Ideal.span {π})) (N k : ℕ) (h3N : 3 ≤ N)
    (d : Dom L N) (ω₀ : Form (HS L N) (k + 1)) (hω₀G : Good ω₀) (hω₀γ : ∀ γ, FInv ω₀ (emb L N γ))
    (hω₀s : ∀ s, FInv ω₀ (scal L N s)) (hLz0 : ∀ u : Fin (k + 1) → HS L N, Lz d (fun x => fr ω₀ x u))
    (z : Chn (Gm L N) (k + 1)) (hz : IsCyc z) :
    ∃ C : ℝ, ∀ r : ℕ, |ev (toK L N) ((hecke (toK L N) (MonoidHom.id (GK L N)) (qel L N π hπ.ne_zero))^[r]
      (fun y => intP ω₀ fun j => toP L N (y j) • one L N)) 1 z| ≤ C * (3 / 5 : ℝ) ^ r := by
  obtain ⟨K, hK0, hK⟩ := lem_nrm (L := L) (N := N) k
  obtain ⟨Cz, hCz⟩ := hLoc L N k (by omega) d z hz
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ := ⟨_, rfl⟩
  refine ⟨|Cz| * √(K * S0), fun r => ?_⟩
  rw [ev_toK _ _ (hecke_iter (qel L N π hπ.ne_zero) hω₀G.1 r) z]
  obtain ⟨ωr, hωr⟩ : ∃ ωr, ωr = (Hk (qel L N π hπ.ne_zero))^[r] ω₀ := ⟨_, rfl⟩
  rw [← hωr]
  obtain ⟨hrG, hrγ, hrs⟩ := Hk_iter_props (qel L N π hπ.ne_zero) hω₀G hω₀γ hω₀s r
  rw [← hωr] at hrG hrγ hrs
  have hLzr : ∀ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      Lz d (fun x => fr ωr x fun i => Module.finBasis ℝ (HS L N) (v i)) ∧
      ∫ x in d.D, fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ ≤
        ((3 / 5 : ℝ) ^ 2) ^ r * ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
    fun v => by
      have := lem_gap hGap hC π hπ hπ25 h3N d _ (hLz0 (fun i => Module.finBasis ℝ (HS L N) (v i))) r
      rw [← comp_Hk_iter, ← hωr] at this
      exact this
  have hsumint : Integrable (fun x => K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2) (d.μ.restrict d.D) :=
    (integrable_finsetSum _ fun v _ => (hLzr v).1.2.2.2.1).const_mul _
  have hint_r : IntegrableOn (fun x => ‖fr ωr (ofS L N x)‖ ^ 2) d.D d.μ :=
    Integrable.mono' hsumint ((lem_meas d hrG.1).norm.pow 2) (Filter.Eventually.of_forall fun x => by
      show ‖‖fr ωr (ofS L N x)‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hK _)
  have hIr : ∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ ≤ ((3 / 5 : ℝ) ^ 2) ^ r * (K * S0) := by
    calc ∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ
        ≤ ∫ x in d.D, K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
            fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
          integral_mono hint_r hsumint fun x => hK _
      _ = K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
            ∫ x in d.D, fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ := by
          rw [integral_const_mul, integral_finsetSum _ fun v _ => (hLzr v).1.2.2.2.1]
      _ ≤ K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)), ((3 / 5 : ℝ) ^ 2) ^ r *
            ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => (hLzr v).2) hK0
      _ = ((3 / 5 : ℝ) ^ 2) ^ r * (K * S0) := by rw [hS0, ← Finset.mul_sum]; ring
  have hsq : √(((3 / 5 : ℝ) ^ 2) ^ r * (K * S0)) = (3 / 5 : ℝ) ^ r * √(K * S0) := by
    rw [← pow_mul, mul_comm 2 r, pow_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  calc |ev (emb L N) (intP ωr) (one L N) z|
      ≤ Cz * √(∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ) := hCz _ hrG hrγ hrs hint_r
    _ ≤ |Cz| * √(((3 / 5 : ℝ) ^ 2) ^ r * (K * S0)) :=
        mul_le_mul (le_abs_self _) (Real.sqrt_le_sqrt hIr) (Real.sqrt_nonneg _) (abs_nonneg _)
    _ = |Cz| * √(K * S0) * (3 / 5 : ℝ) ^ r := by rw [hsq]; ring

end PositivityTheory.KB.JoinReconstruction

end
