import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateEndomorphismUniqueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodGaloisExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodThetaKernelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateLogNeZeroStatement

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK

namespace GlobalTheory.LTPer

theorem sum_sub_sum_mem {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I) (c : ℕ → A) (N : ℕ)
    (hc : ∀ j, N ≤ j → c j = 0) (n : ℕ) :
    ∑ j ∈ Finset.range N, c j * x ^ j - ∑ j ∈ Finset.range n, c j * x ^ j ∈ I ^ n := by
  rcases le_or_gt n N with h | h
  · rw [← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hj).1 (Ideal.pow_mem_pow hx j)
  · rw [← Finset.sum_range_add_sum_Ico _ h.le, sub_add_cancel_left,
      Finset.sum_eq_zero (fun j hj => by rw [hc j (Finset.mem_Ico.1 hj).1, zero_mul]), neg_zero]
    exact Ideal.zero_mem _

variable {l : ℕ} [Fact l.Prime]

theorem coeff_ltSeries (K : FinExt l) (π : ↥(OL K)) (j : ℕ) :
    PowerSeries.coeff j (ltSeries K π) = (if j = 1 then π else 0) + (if j = resCard K then 1 else 0) := by
  rw [ltSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, mul_ite, mul_one,
    mul_zero]

theorem ltSeries_eval (K : FinExt l) (π : ↥(OL K)) (ω : AK K) :
    inO K π * ω + ω ^ resCard K =
      ∑ j ∈ Finset.range (resCard K + 2), inO K (PowerSeries.coeff j (ltSeries K π)) * ω ^ j := by
  simp only [coeff_ltSeries, map_add, add_mul, Finset.sum_add_distrib, apply_ite (inO K), map_zero, map_one,
    ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega), pow_one]

theorem ltSeries_coeff_eq_zero (K : FinExt l) (π : ↥(OL K)) (j : ℕ) (hj : resCard K + 2 ≤ j) :
    inO K (PowerSeries.coeff j (ltSeries K π)) = 0 := by
  rw [coeff_ltSeries, if_neg (by omega), if_neg (by omega), add_zero, map_zero]

end GlobalTheory.LTPer

open GlobalTheory.LTPer in

theorem GlobalTheory.LTPer.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ t : BK K, t ≠ 0 ∧ frobB K t = inK K (π : ↥K.1) * t ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  intro l _ K χ π z hD
  haveI := Formalism.BasicNotions.Examples₂.LB.OL_resFinite K
  have hπ : Irreducible π := hD.1
  obtain ⟨hf, hE⟩ := GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ
  obtain ⟨ω, hω0, hθ, hφ, hg⟩ := GlobalTheory.T.lubin_tate_period_galois_expansion l K χ π z hD
  have hθ' : ω ∈ RingHom.ker (thetaK K) := hθ
  refine ⟨ltLog hπ hf ω hθ, GlobalTheory.T.lubin_tate_log_ne_zero l K π hπ _ hf ω hθ (GlobalTheory.T.lubin_tate_period_theta_kernel l K χ π z hD ω hω0 hθ hφ hg), ?_, fun g => ?_⟩
  · refine ev_log_self hπ hf hθ (y := frobq K ω) (fun n => ?_) (Ev.frob (ev_ltLog hπ hf ω hθ))
    rw [hφ, ltSeries_eval]
    exact sum_sub_sum_mem _ hθ' _ _ (fun j hj => ltSeries_coeff_eq_zero K π j hj) n
  · obtain ⟨a, ha, φ, hφE, -⟩ := hD.2.2.2.2 g
    have hy := hg g a φ ha hφE
    rw [(hE a φ).1 hφE] at hy
    rw [ev_log_hom hπ hf a hθ hy (Ev.gal g (ev_ltLog hπ hf ω hθ)), ← ha]
    rfl

end
