import Formalism.GaussJetBounds.StatementY
import Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
import Formalism.GaussJetBounds.GaussJetProofs.GField
import Formalism.GaussJetBounds.GaussJetProofs.FJEval
import Formalism.GaussJetBounds.GaussJetProofs.Labels

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

namespace GaussB

lemma norm_det_generic {K : Type} [NormedField K] {T : Type} {N0 : ℕ} (p : ℕ) [Fact p.Prime]
    (Y : T × Fin N0 × Fin N0 → K) (hY : IsGeneric p Y) (τ : T) :
    ‖(Matrix.of fun i a : Fin N0 => Y (τ, i, a)).det‖ = 1 := by
  classical
  set M : Matrix (Fin N0) (Fin N0) (MvPolynomial (T × Fin N0 × Fin N0) ℤ) :=
    Matrix.of fun i a => MvPolynomial.X (τ, i, a) with hM
  have h1 : (Matrix.of fun i a : Fin N0 => Y (τ, i, a)).det = MvPolynomial.aeval Y M.det := by
    rw [AlgHom.map_det]
    congr 1
    ext i a
    simp [hM]
  rw [h1]
  refine hY _ fun h0 => ?_
  set ψ : MvPolynomial (T × Fin N0 × Fin N0) ℤ →+* ZMod p :=
    (MvPolynomial.eval (fun y : T × Fin N0 × Fin N0 => if y.2.1 = y.2.2 then (1 : ZMod p) else 0)).comp
      (MvPolynomial.map (Int.castRingHom (ZMod p))) with hψ
  have h2 : ψ M.det = 0 := by
    rw [hψ, RingHom.comp_apply, h0, map_zero]
  rw [RingHom.map_det] at h2
  have h3 : ψ.mapMatrix M = 1 := by
    ext i a
    simp [hM, hψ, Matrix.one_apply]
  rw [h3, Matrix.det_one] at h2
  exact one_ne_zero h2

lemma cc_expo {K : Type} [Field K] {H : Type} [Fintype H] {N0 N1 : ℕ} (S : K) (u : H → K) :
    MvPowerSeries.constantCoeff ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
      MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) :
        MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero, mul_zero]
  intro t _
  rw [map_sum]
  refine Finset.sum_eq_zero fun ab _ => ?_
  simp

lemma map_expo {F K : Type} [Field F] [Field K] (φ : F →+* K) {H : Type} [Fintype H] {N0 N1 : ℕ}
    (S : F) (u : H → F) :
    MvPowerSeries.map φ ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
      MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) :
        MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) F) =
      (-(φ S)) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (φ (u t)) *
        MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2) := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, ← MvPowerSeries.smul_eq_C_mul,
    map_neg]
  simp only [map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_X]

lemma jetsIntegral_map {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K)
    (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {sg : MvPowerSeries ι F} (h : JetsIntegral sg) :
    JetsIntegral (MvPowerSeries.map φ sg) := by
  intro κ
  rw [MvPowerSeries.coeff_map, ← map_natCast φ, ← map_mul, hφ]
  exact h κ

end GaussB

open GaussB in
theorem theorem_B_gauss_sums : ThmBGauss := by
  intro p _ H _ _ N0 N1 S u hS hu sg hsg TT colN ht hht hht1 I nu1 nu2 size hnu1 hnu2 hsize n
  have hpp : p.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists p ((Bool × H) × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnp : ‖(p : K)‖ = ‖(p : ℂ_[p])‖ := by rw [← map_natCast φ, hφ]
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    have h := norm_intCast_padicComplex p (p : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hp0 : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast hpp.ne_zero)
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  have hB := theorem_B.{0} K ‖(p : ℂ_[p])‖ hp0 hp1 H N0 N1 (φ S) (fun t => φ (u t))
    (by rw [hφ]; exact hS) (fun t => by rw [hφ]; exact hu t) _ (jetsIntegral_map φ hφ hsg)
    (fun τ => Matrix.of fun i a : Fin N0 => Y (τ, i, a)) (fun τ i a => hY _)
    (fun τ => norm_det_generic p Y hgen τ) TT colN ht hht hht1 I nu1 nu2 size hnu1 hnu2 hsize
  refine le_trans (le_ciSup (bddAbove_norm_coeff _) n) ?_
  rw [← hgauss, eval₂_jetPairPoly, map_mul, map_mvExp φ _ (cc_expo S u), map_expo, map_prod]
  simp only [ringMap_minorProd, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  exact hB

end Formalism.DworkPowerSeriesWeights
