import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.OmPhiInt

section Num

variable {S : Finset ℕ}

theorem intOff_pow' {z : ℂ} (h : IntOff S z) : ∀ n : ℕ, IntOff S (z ^ n)
  | 0 => by simpa using IntOff.one
  | n + 1 => by rw [pow_succ]; exact (intOff_pow' h n).mul h

theorem intOff_zpow' {z : ℂ} (h : IntOff S z) (h' : IntOff S z⁻¹) : ∀ n : ℤ, IntOff S (z ^ n)
  | (n : ℕ) => by rw [zpow_natCast]; exact intOff_pow' h n
  | Int.negSucc n => by rw [zpow_negSucc, ← inv_pow]; exact intOff_pow' h' _

theorem intOff_of_sq_nat {z : ℂ} {n : ℕ} (h : z ^ 2 = n) : IntOff S z := by
  have hz : z ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp [h]
  refine ⟨hz, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam hz]
  have h1 : (lam ⟨z, hz⟩) ^ 2 = (n : ℂ_[p]) := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : TaylorLogMetric.Qbar) ^ 2 = (n : TaylorLogMetric.Qbar) := Subtype.ext (by simpa using h)
    rw [this, map_natCast]
  have h2 : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  have h3 : ‖lam ⟨z, hz⟩‖ ^ 2 ≤ 1 := by rw [← norm_pow, h1]; exact h2
  nlinarith [norm_nonneg (lam ⟨z, hz⟩)]

theorem one_lt_qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : 1 < Formalism.L2.Col.qOf P := by
  unfold Formalism.L2.Col.qOf
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
  omega

theorem unitV_intOff {E K : Type} [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    IntOff S (σ (LocE.unitV χ a)) ∧ IntOff S (σ (LocE.unitV χ a))⁻¹ := by
  unfold LocE.unitV
  split_ifs with h
  · have hp := GlobalTheory.LastSteps.char_pow χ h.unit
    have hq := one_lt_qOf P
    have e : (σ ((χ h.unit : Kˣ) : K)) ^ (Formalism.L2.Col.qOf P - 1) = 1 := by rw [← map_pow, hp, map_one]
    exact ⟨IntOff.of_pow (by omega) e, IntOff.of_pow (n := Formalism.L2.Col.qOf P - 1) (by omega) (by rw [inv_pow, e, inv_one])⟩
  · simp only [map_zero, inv_zero]
    exact ⟨IntOff.zero, IntOff.zero⟩

theorem locChar_intOff {E K : Type} [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) {P : HeightOneSpectrum (𝓞 E)}
    (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (hc : IntOff S (σ cq)) (hc' : IntOff S (σ cq)⁻¹) :
    IntOff S (σ (LocE.locChar (Formalism.L2.Col.qOf P) cq χ a)) ∧ IntOff S (σ (LocE.locChar (Formalism.L2.Col.qOf P) cq χ a))⁻¹ := by
  unfold LocE.locChar
  rw [map_mul, map_zpow₀, mul_inv, ← zpow_neg]
  obtain ⟨h1, h2⟩ := unitV_intOff (S := S) σ χ (a / ((Formalism.L2.Col.qOf P : ℕ) : E) ^ LocE.vP P (Formalism.L2.Col.qOf P) a)
  exact ⟨(intOff_zpow' hc hc' _).mul h1, (intOff_zpow' hc hc' _).mul h2⟩

end Num

theorem intOff_omPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ (P : rowSG t.Pr t.sel (t.tup μ)) (hal : AutY t.X D.R i) (h : AutY t.X D.R (i + 1)), (P.1 ∈ t.Pr.vGs → hal ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧ h ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1)) → ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P hal h x)) := by
  intro D L hT Gi Gl K Y cX ex t hmu0 hval u μ hQg i hi P hal h hstab x
  have hok := (t.idx_ok μ).cst_ok
  have hS : SNum (t.O u μ).S (Formalism.L2.Col.qOf P.1) := GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P
  have hs2 : (t.seam.σ₀ ((t.cst μ).sq P)) ^ 2 = ((Formalism.L2.Col.qOf P.1 : ℕ) : ℂ) := by
    rw [← map_pow, hok.sq_sq P, map_natCast]
  have hs0 : t.seam.σ₀ ((t.cst μ).sq P) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    have := one_lt_qOf P.1
    have h1 : ((Formalism.L2.Col.qOf P.1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact h1 hs2.symm
  have hsq : IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).sq P)) := intOff_of_sq_nat hs2
  have hsq' : IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).sq P))⁻¹ := by
    have e : (t.seam.σ₀ ((t.cst μ).sq P))⁻¹ = t.seam.σ₀ ((t.cst μ).sq P) * (((Formalism.L2.Col.qOf P.1 : ℕ) : ℂ))⁻¹ := by
      rw [← hs2, pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    rw [e]
    exact hsq.mul (IntOff.inv_nat hS)
  have hmu : ∀ a : t.X.E, (P.1 ∈ t.Pr.vGs → IsUnit (redP P.1 a)) →
      IntOff (t.O u μ).S (t.seam.σ₀ (Formalism.L2.Col.muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P a)) ∧
        IntOff (t.O u μ).S (t.seam.σ₀ (Formalism.L2.Col.muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P a))⁻¹ := by
    intro a ha
    unfold Formalism.L2.Col.muAt
    by_cases hP : P.1 ∈ t.Pr.vGs
    · rw [GlobalTheory.LastSteps.locChar_unit _ _ (ha hP)]
      exact unitV_intOff _ _ _
    · obtain ⟨h1, h2⟩ := GlobalTheory.KerTie.muq_intOff D L hT Gi Gl K Y cX ex t hmu0 hval u μ hQg i hi P hP
      rw [map_inv₀] at h2
      exact locChar_intOff _ _ _ _ h1 h2
  have hPhi := (GlobalTheory.PhiRootVal.phi_intOff D L hT Gi Gl K Y cX ex t u μ P.1).1 i
  have hA := hmu ((LinearEquiv.det hal : t.X.Eˣ) : t.X.E) fun hP => GlobalTheory.LastSteps.isUnit_det_of_stab (hstab hP).1
  have hB := hmu ((LinearEquiv.det h : t.X.Eˣ) : t.X.E) fun hP => GlobalTheory.LastSteps.isUnit_det_of_stab (hstab hP).2
  unfold Formalism.L2.Col.omPhi Loc.om
  rw [map_mul, map_mul, map_mul, map_mul, map_inv₀, map_zpow₀, map_zpow₀]
  exact (((hA.1.mul hB.2).mul (intOff_zpow' hsq hsq' _)).mul (intOff_zpow' hsq hsq' _)).mul (hPhi _)

end GlobalTheory.OmPhiInt
