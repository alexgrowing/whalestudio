import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

theorem GlobalTheory.WinLift.frob_lift_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V F0 hV hF hθ i m
  set ξ' : Ainf p O := WittVector.frobenius (xi ε) with hξ'
  set μ : Ainf p O := Sandwich.mu ε with hμ
  set G : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) := V.transpose * F0 with hG
  set E : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) :=
    blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • G with hEdef
  have hVt : IsUnit V.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det V).1 hV
  have key : V.transpose⁻¹ * blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • F0 =
      V.transpose⁻¹ * E := by
    rw [hEdef, hG, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc (V.transpose⁻¹),
      Matrix.nonsing_inv_mul _ hVt, Matrix.one_mul]
  have hEe : ∀ j n, E j n = Sum.elim (fun _ => (1 : Ainf p O)) (fun _ => ξ') j *
      WittVector.frobenius (F0 j n) - ξ' * G j n := by
    intro j n
    simp [hEdef, blk, Matrix.diagonal_mul]
  have hyp : ∀ j n, μ ∣ WittVector.frobenius (F0 j n) -
      Sum.elim (fun _ => (p : Ainf p O)) (fun _ => 1) j * G j n := by
    intro j n
    have := hF j n
    rw [Matrix.mul_assoc, ← hG] at this
    simpa [blk, Matrix.diagonal_mul] using this
  have hE : ∀ j n, ξ' * μ ∣ E j n := by
    intro j n
    rw [hEe]
    rcases j with j | j
    · obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton').1
        (show F0 (Sum.inl j) n ∈ Ideal.span {xi ε} by
          rw [← AinfXi.ker_theta hv ε (root_prim hε)]; exact hθ j n)
      have h1 : μ ∣ ξ' * (WittVector.frobenius w - G (Sum.inl j) n) := by
        have := dvd_sub (hyp (Sum.inl j) n) ((mu_dvd_frob_xi_sub ε).mul_right (G (Sum.inl j) n))
        convert this using 1
        simp only [Sum.elim_inl]
        rw [← hw, map_mul, ← hξ']
        ring
      have h2 := mul_dvd_mul_left ξ' (mu_dvd_of_xi_mul F _ h1)
      convert h2 using 1
      simp only [Sum.elim_inl]
      rw [← hw, map_mul, ← hξ']
      ring
    · have := mul_dvd_mul_left ξ' (hyp (Sum.inr j) n)
      convert this using 1
      simp only [Sum.elim_inr]
      ring
  have e := congrFun (congrFun key i) m
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e
  rw [e, Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => (hE j m).mul_left _
