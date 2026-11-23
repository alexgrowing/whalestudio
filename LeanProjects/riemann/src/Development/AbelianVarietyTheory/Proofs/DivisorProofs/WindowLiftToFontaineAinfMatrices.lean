import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusXiEqPMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfFrameLiftTwistedFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTauStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMatrixLiftModTauAinfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentInvTransposeBlockFrobeniusAinfOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSolutionOfApproxModPhiXiMuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdLiftOfFrameMatrixEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftSolvesModFrobXiMuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTransposeStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift.Top

theorem c_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := GlobalTheory.T.exists_unit_matrix_lift_mod_tau_ainf

theorem c_nilF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := GlobalTheory.T.isNilpotent_invTranspose_blockFrobenius_ainf_of_frameNil

theorem c_nilG : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := GlobalTheory.T.isNilpotent_blockFrobeniusXi_ainf_of_frameBlockP

theorem c_solve : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := GlobalTheory.T.exists_ainf_solution_of_approx_mod_phi_xi_mu

theorem c_modtau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := GlobalTheory.T.mu_dvd_lift_of_frame_matrix_equation

theorem c_divF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := GlobalTheory.T.frobenius_lift_solves_mod_frobXi_mu

theorem c_divG : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := GlobalTheory.T.transpose_lift_solves_mod_frobXi_mu

theorem c_eig : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := GlobalTheory.T.frobXi_eigenvector_eq_of_frame_image_eq

theorem c_cmpF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := GlobalTheory.T.ainfFrame_solution_congr_eq_transpose_mul

theorem c_cmpG : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := GlobalTheory.T.ainfFrame_solution_mul_congr_Gm_transpose

theorem frob_phiInv {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_frob {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    phiInv p O (WittVector.frobenius a) = a := by
  ext n
  rw [phiInv, WittVector.map_coeff, WittVector.coeff_frobenius_charP]
  exact (_root_.frobeniusEquiv (PreTilt O p) p).symm_apply_apply _

theorem blk_mul_blk {R : Type} [CommRing R] (d k : ℕ) (a b c e : R) :
    blk d k a b * blk d k c e = blk d k (a * c) (b * e) := by
  rw [blk, blk, blk, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem blk_same {R : Type} [CommRing R] (d k : ℕ) (a : R) :
    blk d k a a = a • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  ext i j
  simp only [blk, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij; rcases i with i | i <;> simp
  · simp

theorem blk_transpose {R : Type} [CommRing R] (d k : ℕ) (a b : R) :
    (blk d k a b).transpose = blk d k a b := Matrix.diagonal_transpose _

theorem blk_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d k : ℕ) (a b : R) :
    (blk d k a b).map f = blk d k (f a) (f b) := by
  rw [blk, blk, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem c_nilCong : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U U' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsUnit U' → (∀ i j, F.τ ∣ U i j - U' i j) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U U' hU hU' hUU' h1 h2
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  have hθτ := theta_tau F hv hε
  have hθ : ∀ i j, F.θ (U i j) = F.θ (U' i j) := by
    intro i j
    obtain ⟨c, hc⟩ := hUU' i j
    rw [← sub_eq_zero, ← map_sub, hc, map_mul, hθτ, zero_mul]
  have hp : ¬IsUnit (p : O) := Fact.out
  have hmap : U.map F.θ = U'.map F.θ := Matrix.ext hθ
  have htu : ∀ M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit M → IsUnit M.transpose :=
    fun M hM => (Matrix.isUnit_iff_isUnit_det _).2
      (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hM)
  have e : ∀ M : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit M → ∀ i j,
      F.θ ((M.transpose⁻¹ * blk d k 1 (p : F.B)) i j) =
        (((M.map F.θ).transpose)⁻¹ * blk d k 1 (p : O)) i j := by
    intro M hM i j
    have := congr_fun (congr_fun (Matrix.map_mul (f := F.θ) (L := M.transpose⁻¹)
      (M := blk d k 1 (p : F.B))) i) j
    rw [Matrix.map_apply] at this
    rw [this, ← map_inv_of_isUnit F.θ _ (htu M hM), Matrix.transpose_map, blk_map, map_one,
      map_natCast]
  refine ⟨isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) h1,
    isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) h2⟩
  · rw [e U hU, e U' hU', hmap]
  · simp only [blk, Matrix.mul_diagonal, map_mul, hθ]

theorem window_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U Y Gm hyp
  obtain ⟨hU, hY, hG, hGY, hYθ, hGθ, hN1, hN2⟩ := hyp
  haveI : IsDomain (Ainf p O) := GlobalTheory.AinfXi.isDomain_ainf hv
  have hθτ : F.θ F.τ = 0 := theta_tau F hv hε
  have hξ0 : WittVector.frobenius (xi ε) ≠ 0 := by
    intro h0
    have h1 := theta_frob_xi hv hε
    rw [h0, map_zero] at h1
    have h2 := congrArg (algebraMap O C) h1
    rw [map_zero, map_natCast] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2.symm
  obtain ⟨V, hV, hUV⟩ := c_lift p C v O hv ε hε F _ U hU
  obtain ⟨F0, F1, hF0⟩ : ∃ F0 F1 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O),
      ∀ i m, Y i m = F.a (F0 i m) + F.τ * F.a (F1 i m) := by
    choose F0 F1 hF0 using fun i m => F.gen (Y i m)
    exact ⟨F0, F1, hF0⟩
  obtain ⟨G0, G1, hG0⟩ : ∃ G0 G1 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O),
      ∀ i m, Gm m i = F.a (G0 i m) + F.τ * F.a (G1 i m) := by
    choose G0 G1 hG0 using fun (i : Fin d ⊕ Fin k) (m : Fin h) => F.gen (Gm m i)
    exact ⟨G0, G1, hG0⟩
  have hYF : ∀ i m, F.τ ∣ Y i m - F.a (F0 i m) := fun i m => ⟨F.a (F1 i m), by rw [hF0 i m]; ring⟩
  have hGG : ∀ i m, F.τ ∣ Gm m i - F.a (G0 i m) := fun i m => ⟨F.a (G1 i m), by rw [hG0 i m]; ring⟩
  have hθY : ∀ i m, WittVector.fontaineTheta O p (F0 i m) = F.θ (Y i m) := by
    intro i m; rw [hF0 i m, map_add, map_mul, hθτ, zero_mul, add_zero, F.θ_a]
  have hθG : ∀ i m, WittVector.fontaineTheta O p (G0 i m) = F.θ (Gm m i) := by
    intro i m; rw [hG0 i m, map_add, map_mul, hθτ, zero_mul, add_zero, F.θ_a]
  have hdvdμ : ∀ x : Ainf p O, Sandwich.mu ε ∣ x → F.τ ∣ F.a x := by
    rintro x ⟨c, rfl⟩; rw [map_mul, ← F.p_τ]; exact ⟨p * F.a c, by ring⟩
  have hone : ∀ i j, F.τ ∣ (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j -
      F.a ((1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) i j) := by
    intro i j; simp only [Matrix.one_apply]; split_ifs <;> simp
  have hpone : ∀ i j, F.τ ∣ ((p : F.B) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B)) i j -
      F.a (((p : Ainf p O) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))) i j) := by
    intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp
  have hel : ∀ (x : F.B) (y : Ainf p O), F.a y = x → ∀ i : Fin d ⊕ Fin k,
      F.a (Sum.elim (fun _ => y) (fun _ => (1 : Ainf p O)) i) = Sum.elim (fun _ => x) (fun _ => 1) i := by
    intro x y hxy i; rcases i with i | i <;> simp [hxy]
  have hL : ∀ i j, F.τ ∣ (blk d k (p : F.B) 1 * U.transpose) i j -
      F.a ((blk d k (p : Ainf p O) 1 * V.transpose) i j) := by
    intro i j
    simp only [blk, Matrix.diagonal_mul, Matrix.transpose_apply, map_mul]
    rw [hel (p : F.B) (p : Ainf p O) (map_natCast _ _) i, ← mul_sub]
    exact dvd_mul_of_dvd_right (hUV j i) _
  have hR : ∀ i j, F.τ ∣ (U * blk d k (p : F.B) 1) i j -
      F.a ((V * blk d k (p : Ainf p O) 1) i j) := by
    intro i j
    simp only [blk, Matrix.mul_diagonal, map_mul]
    rw [hel (p : F.B) (p : Ainf p O) (map_natCast _ _) j, ← sub_mul]
    exact dvd_mul_of_dvd_left (hUV i j) _

  have hF0μ : ∀ i m, Sandwich.mu ε ∣ (F0.map
      WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m := by
    have := c_modtau p C v O hv ε hε F _ (Fin h) 1 (blk d k (p : F.B) 1 * U.transpose) 1
      (blk d k (p : Ainf p O) 1 * V.transpose) Y F0 hone hL hYF (by rw [Matrix.one_mul, hY])
    simpa only [Matrix.one_mul] using this
  have hdivF := c_divF p C v O hv ε hε F d k h V F0 hV hF0μ (fun i m => by rw [hθY]; exact hYθ i m)
  have hnilF := c_nilF p C v O hv ε hε F d k U V hU hV hUV hN2
  choose Fw hFw1 hFw2 using fun m : Fin h => c_solve p C v O hv ε hε _
    (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) (fun i => F0 i m) hnilF
    (fun i => hdivF i m)

  set ξ' := WittVector.frobenius (xi ε) with hξ'
  let Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) := Matrix.of fun i m => Fw m i
  have hFaeq : ξ' • Fa = (V.transpose⁻¹ * blk d k 1 ξ') * Fa.map WittVector.frobenius := by
    exact Matrix.ext fun i m => hFw2 m i
  have hdetV : IsUnit V.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det V).1 hV
  have hφFa : Fa.map WittVector.frobenius = blk d k ξ' 1 * V.transpose * Fa := by
    have e1 : V.transpose * (ξ' • Fa) = blk d k 1 ξ' * Fa.map WittVector.frobenius := by
      rw [hFaeq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetV,
        Matrix.one_mul]
    have e2 : ξ' • (blk d k ξ' 1 * V.transpose * Fa) = ξ' • Fa.map WittVector.frobenius := by
      rw [Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.mul_smul, e1, ← Matrix.mul_assoc, blk_mul_blk, mul_one,
        one_mul, blk_same, Matrix.smul_mul, Matrix.one_mul]
    refine Matrix.ext fun i m => ?_
    have := congr_fun (congr_fun e2 i) m
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact (mul_left_cancel₀ hξ0 this).symm
  let Ψ := (blk d k ξ' 1 * V.transpose).map (phiInv p O)
  let Ψ' := (V.transpose⁻¹ * blk d k 1 ξ').map (phiInv p O)
  have hfinj : ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius y → x = y :=
    fun x y hxy => by rw [← phiInv_frob x, hxy, phiInv_frob]
  have hFaΨ : Fa = Ψ * Fa.map (phiInv p O) := by
    have : (Ψ * Fa.map (phiInv p O)).map WittVector.frobenius = Fa.map WittVector.frobenius := by
      rw [Matrix.map_mul, hφFa, Matrix.map_map, Matrix.map_map]
      have h1 : (WittVector.frobenius ∘ phiInv p O) = id := funext frob_phiInv
      rw [h1, Matrix.map_id, Matrix.map_id]
    refine Matrix.ext fun i m => ?_
    exact (hfinj _ _ (congr_fun (congr_fun this i) m)).symm
  have hΨΨ' : Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) := by
    have e : blk d k ξ' 1 * V.transpose * (V.transpose⁻¹ * blk d k 1 ξ') =
        ξ' • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.transpose, Matrix.mul_nonsing_inv _ hdetV,
        Matrix.one_mul, blk_mul_blk, mul_one, one_mul, blk_same]
    rw [← Matrix.map_mul, e]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [hξ', phiInv_frob]

  have hG0μ : ∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius -
      (p : Ainf p O) • G0) i m := by
    have := c_modtau p C v O hv ε hε F _ (Fin h) (U * blk d k (p : F.B) 1)
      ((p : F.B) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B)) (V * blk d k (p : Ainf p O) 1)
      ((p : Ainf p O) • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))) Gm.transpose G0
      hR hpone (fun i m => hGG i m) (by rw [hG, Matrix.smul_mul, Matrix.one_mul])
    simpa only [Matrix.smul_mul, Matrix.one_mul] using this
  have hdivG := c_divG p C v O hv ε hε F d k h V G0 hG0μ (fun j m => by rw [hθG]; exact hGθ m j)
  have hnilG := c_nilG p C v O hv ε hε F d k U V hUV hN1
  choose Gw hGw1 hGw2 using fun m : Fin h => c_solve p C v O hv ε hε _
    (V * blk d k ξ' 1) (fun i => G0 i m) hnilG (fun i => hdivG i m)
  let Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O) := Matrix.of fun m i => Gw m i
  have hGaeq : ξ' • Ga.transpose = V * blk d k ξ' 1 * Ga.transpose.map WittVector.frobenius :=
    Matrix.ext fun i m => hGw2 m i
  have hφP : (Ga * Fa).map WittVector.frobenius = ξ' • (Ga * Fa) := by
    have e : ξ' • Ga = Ga.map WittVector.frobenius * blk d k ξ' 1 * V.transpose := by
      have := congrArg Matrix.transpose hGaeq
      rw [Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_mul,
        Matrix.transpose_mul, blk_transpose, Matrix.transpose_map, Matrix.transpose_transpose,
        ← Matrix.mul_assoc] at this
      exact this
    rw [Matrix.map_mul, hφFa, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← e, Matrix.smul_mul]

  obtain ⟨u, hu, hτu, hau⟩ := GlobalTheory.T.frobenius_xi_eq_p_mul_unit p C v O hv ε hε F
  obtain ⟨l, hτl, hσl⟩ := GlobalTheory.T.exists_ainf_frame_lift_twisted_frobenius p C v O hv ε hε F u hτu
  let U' := V.map F.a * blk d k u 1
  have hU' : IsUnit U' := by
    refine IsUnit.mul ?_ ?_
    · exact hV.map (RingHom.mapMatrix F.a)
    · refine Matrix.isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i => ?_)
      rcases i with i | i
      · exact hu
      · exact isUnit_one
  have hUU' : ∀ i j, F.τ ∣ U i j - U' i j := by
    intro i j
    simp only [U', blk, Matrix.mul_diagonal, Matrix.map_apply]
    rcases j with j | j
    · have : U i (Sum.inl j) - F.a (V i (Sum.inl j)) * u =
          (U i (Sum.inl j) - F.a (V i (Sum.inl j))) - F.a (V i (Sum.inl j)) * (u - 1) := by ring
      simp only [Sum.elim_inl]
      rw [this]
      exact dvd_sub (hUV _ _) (dvd_mul_of_dvd_right hτu _)
    · simp only [Sum.elim_inr, mul_one]
      exact hUV _ _
  obtain ⟨X, hX1, hX2⟩ := GlobalTheory.T.isIso_windows_of_matrix_congr_mod_tau p C v O hv ε hε F d k U U' hU hU' hUU' hN1
  obtain ⟨hn1', hn2'⟩ := c_nilCong p C v O hv ε hε F d k U U' hU hU' hUU' hN2 hN1
  have haξ : F.a ξ' = (p : F.B) * u := hau
  let Z := Fa.map F.a
  have hZσ : Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z := by
    have e1 : Z.map F.σ = (Fa.map WittVector.frobenius).map F.a :=
      Matrix.ext fun i m => F.σ_a _
    rw [e1, hφFa, Matrix.map_mul, Matrix.map_mul, blk_map, haξ, map_one, Matrix.transpose_map]
    show _ = blk d k (p : F.B) 1 * (V.map F.a * blk d k u 1).transpose * Fa.map F.a
    rw [Matrix.transpose_mul, blk_transpose, ← Matrix.mul_assoc (blk d k (p : F.B) 1), blk_mul_blk,
      mul_one]
  have hZY : ∀ i m, F.τ ∣ Z i m - Y i m := by
    intro i m
    have e : Z i m - Y i m = F.a (Fw m i - F0 i m) - (Y i m - F.a (F0 i m)) := by
      simp only [Z, Fa, Matrix.map_apply, Matrix.of_apply, map_sub]; ring
    rw [e]
    exact dvd_sub (hdvdμ _ (hFw1 m i)) (hYF i m)
  have hZ := c_cmpF p C v O hv ε hε F d k h U U' X Y Z hU' hn1' hn2' hX2 hX1 hY hZσ hZY
  let W := Ga.transpose.map F.a
  have hWσ : U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W := by
    have e1 : W.map F.σ = (Ga.transpose.map WittVector.frobenius).map F.a :=
      Matrix.ext fun i m => F.σ_a _
    have hGaeq' : blk d k ξ' ξ' * Ga.transpose = V * blk d k ξ' 1 * Ga.transpose.map WittVector.frobenius := by
      rw [blk_same, Matrix.smul_mul, Matrix.one_mul]; exact hGaeq
    have e2 := congrArg (fun M => M.map F.a) hGaeq'
    simp only [Matrix.map_mul, blk_map, haξ, map_one] at e2
    have e3 : U' * blk d k (p : F.B) 1 = V.map F.a * blk d k ((p : F.B) * u) 1 := by
      show V.map F.a * blk d k u 1 * blk d k (p : F.B) 1 = _
      rw [Matrix.mul_assoc, blk_mul_blk, mul_comm u, mul_one]
    rw [e1, e3, ← e2, blk_same, Matrix.smul_mul, Matrix.one_mul]

  have hWG : ∀ i m, F.τ ∣ W i m - Gm m i := by
    intro i m
    have e : W i m - Gm m i = F.a (Gw m i - G0 i m) - (Gm m i - F.a (G0 i m)) := by
      simp only [W, Ga, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, map_sub]; ring
    rw [e]
    exact dvd_sub (hdvdμ _ (hGw1 m i)) (hGG i m)
  have hXW := c_cmpG p C v O hv ε hε F d k h U U' X u l Gm W hU hN2 hN1 hτu hX2 hX1 hσl hτl hG hWσ hWG
  have hlμ : l * F.a (Sandwich.mu ε) = F.a (Sandwich.mu ε) := by
    obtain ⟨c, hc⟩ := hτl
    rw [← F.p_τ, sub_eq_iff_eq_add.1 hc]
    linear_combination (p * c) * F.τ_sq
  have hprod : (Ga * Fa).map F.a = F.a (Sandwich.mu ε) •
      (1 : Matrix (Fin h) (Fin h) F.B) := by
    have eW : Ga.map F.a = W.transpose := by
      simp only [W, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [Matrix.map_mul, eW, show Fa.map F.a = Z from rfl, hZ, ← Matrix.mul_assoc,
      ← Matrix.transpose_mul, hXW, Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.smul_mul, hGY, smul_smul, hlμ]
  have hGaFa : Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    refine Matrix.ext fun i j => ?_
    refine c_eig p C v O hv ε hε F _ _ ?_ ?_ ?_
    · have := congr_fun (congr_fun hφP i) j
      simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
    · simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp only [mul_one, mul_zero, map_zero, frob_mu]
    · have := congr_fun (congr_fun hprod i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this ⊢
      rw [this]
      split_ifs <;> simp
  refine ⟨Fa, Ga, Ψ, Ψ', hGaFa, hFaΨ, hΨΨ', fun i m => ?_, fun m i => ?_⟩
  · obtain ⟨c, hc⟩ := hFw1 m i
    show WittVector.fontaineTheta O p (Fw m i) = _
    rw [sub_eq_iff_eq_add.1 hc, map_add, map_mul, theta_mu hv hε, zero_mul, zero_add, hθY]
  · obtain ⟨c, hc⟩ := hGw1 m i
    show WittVector.fontaineTheta O p (Gw m i) = _
    rw [sub_eq_iff_eq_add.1 hc, map_add, map_mul, theta_mu hv hε, zero_mul, zero_add, hθG]

end GlobalTheory.WinLift.Top
