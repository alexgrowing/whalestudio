import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubAbscissaEqOneOfUnitDiscrIntegralChordsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormTangentDenominatorEqOneOfUnitDiscrDoubleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelChordLawSumAndDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelTangentLawAtDoubleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaAddMulSubAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOtherHalfPeriodStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

theorem lamC_mul' (lam : Qbar →+* ℂ_[p]) {a b : ℂ} (ha : a ∈ Qbar) (hb : b ∈ Qbar) :
    lamC lam (a * b) = lamC lam a * lamC lam b := by
  unfold lamC
  rw [dif_pos (mul_mem ha hb), dif_pos ha, dif_pos hb, ← map_mul]; rfl

theorem lamC_sub' (lam : Qbar →+* ℂ_[p]) {a b : ℂ} (ha : a ∈ Qbar) (hb : b ∈ Qbar) :
    lamC lam (a - b) = lamC lam a - lamC lam b := by
  unfold lamC
  rw [dif_pos (sub_mem ha hb), dif_pos ha, dif_pos hb, ← map_sub]; rfl

theorem lamC_neg' (lam : Qbar →+* ℂ_[p]) {a : ℂ} (ha : a ∈ Qbar) :
    lamC lam (-a) = -lamC lam a := by
  unfold lamC
  rw [dif_pos (neg_mem ha), dif_pos ha, ← map_neg]; rfl

theorem lamC_pow' (lam : Qbar →+* ℂ_[p]) {a : ℂ} (ha : a ∈ Qbar) (n : ℕ) :
    lamC lam (a ^ n) = lamC lam a ^ n := by
  unfold lamC
  rw [dif_pos (pow_mem ha n), dif_pos ha, ← map_pow]; rfl

theorem lamC_ne_zero' (lam : Qbar →+* ℂ_[p]) {a : ℂ} (ha : a ∈ Qbar) (h : a ≠ 0) :
    lamC lam a ≠ 0 := by
  unfold lamC
  rw [dif_pos ha]
  exact (map_ne_zero lam).2 fun h' => h (congrArg Subtype.val h')

theorem ctx (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) (hg : GL3Theta.At D cc δ g) :
    IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧
    (∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar ∧ wpD g.abelian₂ t ∈ Qbar) ∧
    (∀ t, InRationalLattice g.abelian₂ t → U1 g.abelian₂ t (sgStar g.abelian₂) 0 ∈ Qbar) ∧
    ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧
    ‖g.W.a₁‖ ≤ 1 ∧ ‖g.W.a₂‖ ≤ 1 ∧ ‖g.W.a₃‖ ≤ 1 ∧ ‖g.W.a₄‖ ≤ 1 ∧ ‖g.W.a₆‖ ≤ 1 ∧
    ‖g.W.Δ‖ = 1 := by
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  obtain ⟨hu, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  obtain ⟨⟨h1, h2', h3', h4, h6, hΔ⟩, -⟩ := hok
  refine ⟨hlat', h2, h3, hwp, fun t ht => ?_, hu, h1, h2', h3', h4, h6, hΔ⟩
  have := huse t ht 0
  simpa [coef1] using this

theorem tors_laq {Λ : AddSubgroup ℂ} {t : ℂ} (h : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * t ∈ Λ) :
    InRationalLattice Λ t := by
  obtain ⟨n, hn, -, h⟩ := h
  exact ⟨n, hn, h⟩

theorem natmul_mem {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) (k : ℕ) : (k : ℂ) * w ∈ Λ := by
  have := AddSubgroup.nsmul_mem Λ hw k
  rwa [nsmul_eq_mul] at this

theorem tors_add {Λ : AddSubgroup ℂ} {s t : ℂ} (hs : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * s ∈ Λ)
    (ht : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * t ∈ Λ) :
    ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * (s + t) ∈ Λ := by
  obtain ⟨n, hn, hnp, hs⟩ := hs
  obtain ⟨k, hk, hkp, ht⟩ := ht
  refine ⟨n * k, Nat.mul_pos hn hk, Nat.coprime_mul_iff_left.2 ⟨hnp, hkp⟩, ?_⟩
  have e : ((n * k : ℕ) : ℂ) * (s + t) = (k : ℂ) * ((n : ℂ) * s) + (n : ℂ) * ((k : ℂ) * t) := by
    push_cast; ring
  rw [e]
  exact add_mem (natmul_mem hs k) (natmul_mem ht n)

theorem tors_neg {Λ : AddSubgroup ℂ} {s : ℂ} (hs : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * s ∈ Λ) :
    ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * (-s) ∈ Λ := by
  obtain ⟨n, hn, hnp, hs⟩ := hs
  exact ⟨n, hn, hnp, by rw [mul_neg]; exact neg_mem hs⟩

theorem tors_sub {Λ : AddSubgroup ℂ} {s t : ℂ} (hs : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * s ∈ Λ)
    (ht : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * t ∈ Λ) :
    ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * (s - t) ∈ Λ := by
  rw [sub_eq_add_neg]; exact tors_add hs (tors_neg ht)

theorem tors_two {Λ : AddSubgroup ℂ} {s : ℂ} (hs : ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * s ∈ Λ) :
    ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * (2 * s) ∈ Λ := by
  have := tors_add hs hs
  rwa [← two_mul] at this

theorem logc_eq_of_norm {g : GL3Theta.G1 p} {s t : ℂ} (hs : s ∉ g.abelian₂) (ht : t ∉ g.abelian₂)
    (h : ‖cval g s‖ = ‖cval g t‖) : logc g s = logc g t := by
  simp only [logc, if_neg hs, if_neg ht, h]

theorem thetaTranslateValueAtZero_neg {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) (t : ℂ) :
    U1 Λ (-t) (sgStar Λ) 0 = -U1 Λ t (sgStar Λ) 0 := by
  simp only [U1, zero_add, hlat.sg_neg, map_neg]
  ring_nf

theorem cval_ne_zero {g : GL3Theta.G1 p} (hlat : IsLat g.abelian₂) {t : ℂ} (ht : t ∉ g.abelian₂)
    (hc : U1 g.abelian₂ t (sgStar g.abelian₂) 0 ∈ Qbar) : cval g t ≠ 0 := by
  refine lamC_ne_zero' g.lam hc ?_
  simp only [U1, zero_add, ne_eq, mul_eq_zero, Complex.exp_ne_zero, or_false]
  exact fun h => ht ((hlat.sg_eq_zero t).1 h)

theorem generic (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) (hg : GL3Theta.At D cc δ g)
    (hx : ∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖xAt g s‖ ≤ 1) (P Q : ℂ)
    (hP : GL3Theta.Tors1 p g.abelian₂ P) (hQ : GL3Theta.Tors1 p g.abelian₂ Q) (h1 : P + Q ∉ g.abelian₂) (h2 : P - Q ∉ g.abelian₂) :
    logc g (P + Q) + logc g (P - Q) = 2 * logc g P + 2 * logc g Q := by
  obtain ⟨hlat, hg2, hg3, hwp, hc, hu, ha1, ha2, -, -, -, hΔ⟩ := ctx D cc δ g hg
  have hS : GL3Theta.Tors1 p g.abelian₂ (P + Q) := ⟨h1, tors_add hP.2 hQ.2⟩
  have hD : GL3Theta.Tors1 p g.abelian₂ (P - Q) := ⟨h2, tors_sub hP.2 hQ.2⟩
  obtain ⟨wP, dP⟩ := hwp P (tors_laq hP.2) hP.1
  obtain ⟨wQ, dQ⟩ := hwp Q (tors_laq hQ.2) hQ.1
  obtain ⟨eP, -⟩ := GlobalTheory.T.padicModel_equation_tangent_at_latticeParameter g P hlat hg2 hg3 hP.1 wP dP
  obtain ⟨eQ, -⟩ := GlobalTheory.T.padicModel_equation_tangent_at_latticeParameter g Q hlat hg2 hg3 hQ.1 wQ dQ
  obtain ⟨hne, hadd, hsub⟩ := GlobalTheory.T.padicModel_chordLaw_sum_and_difference g P Q hlat hg2 hg3 hP.1 hQ.1 h1 h2 wP dP wQ dQ
  have hne' : xAt g P - xAt g Q ≠ 0 := sub_ne_zero.2 hne
  have hone := GlobalTheory.T.norm_sub_abscissa_eq_one_of_unitDiscr_integral_chords g.W (xAt g P) (yAt g P) (xAt g Q) (yAt g Q) _ _ ha1 ha2 hΔ eP eQ
    (hx P hP) (hx Q hQ) hne (div_mul_cancel₀ _ hne') (div_mul_cancel₀ _ hne')
    (by rw [← hadd]; exact hx _ hS) (by rw [← hsub]; exact hx _ hD)
  have ediff : xAt g P - xAt g Q =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC g.lam (wpF g.abelian₂ Q) - lamC g.lam (wpF g.abelian₂ P)) * (-1) := by
    unfold xAt; ring
  have hwone : ‖lamC g.lam (wpF g.abelian₂ Q) - lamC g.lam (wpF g.abelian₂ P)‖ = 1 := by
    rw [ediff, norm_mul, norm_mul, norm_pow, hu, norm_neg, norm_one] at hone
    simpa using hone
  have key := GlobalTheory.T.U1_add_mul_U1_sub_at_zero_eq_wpF_sub g.abelian₂ hlat P Q hP.1 hQ.1
  have cS := hc _ (tors_laq hS.2)
  have cD := hc _ (tors_laq hD.2)
  have cP := hc _ (tors_laq hP.2)
  have cQ := hc _ (tors_laq hQ.2)
  have key' := congrArg (lamC g.lam) key
  rw [lamC_mul' _ cS cD, lamC_mul' _ (mul_mem (sub_mem wQ wP) (pow_mem cP 2)) (pow_mem cQ 2),
    lamC_mul' _ (sub_mem wQ wP) (pow_mem cP 2), lamC_sub' _ wQ wP, lamC_pow' _ cP, lamC_pow' _ cQ] at key'
  have hn := congrArg norm key'
  simp only [norm_mul, norm_pow, hwone, one_mul] at hn
  change ‖cval g (P + Q)‖ * ‖cval g (P - Q)‖ = ‖cval g P‖ ^ 2 * ‖cval g Q‖ ^ 2 at hn
  have nS := norm_pos_iff.2 (cval_ne_zero hlat h1 cS)
  have nD := norm_pos_iff.2 (cval_ne_zero hlat h2 cD)
  have nP := norm_pos_iff.2 (cval_ne_zero hlat hP.1 cP)
  have nQ := norm_pos_iff.2 (cval_ne_zero hlat hQ.1 cQ)
  have hl := congrArg Real.log hn
  rw [Real.log_mul nS.ne' nD.ne', Real.log_mul (pow_pos nP 2).ne' (pow_pos nQ 2).ne', Real.log_pow,
    Real.log_pow] at hl
  simp only [logc, if_neg h1, if_neg h2, if_neg hP.1, if_neg hQ.1]
  push_cast at hl
  linarith

theorem doubling (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) (hg : GL3Theta.At D cc δ g)
    (hx : ∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖xAt g s‖ ≤ 1) (P : ℂ)
    (hP : GL3Theta.Tors1 p g.abelian₂ P) (h2 : 2 * P ∉ g.abelian₂) : logc g (2 * P) = 4 * logc g P := by
  obtain ⟨hlat, hg2, hg3, hwp, hc, hu, ha1, ha2, ha3, ha4, ha6, hΔ⟩ := ctx D cc δ g hg
  have hS : GL3Theta.Tors1 p g.abelian₂ (2 * P) := ⟨h2, tors_two hP.2⟩
  obtain ⟨wP, dP⟩ := hwp P (tors_laq hP.2) hP.1
  obtain ⟨eP, hη⟩ := GlobalTheory.T.padicModel_equation_tangent_at_latticeParameter g P hlat hg2 hg3 hP.1 wP dP
  obtain ⟨hne, hdbl⟩ := GlobalTheory.T.padicModel_tangentLaw_at_double g P hlat hg2 hg3 hP.1 h2 wP dP
  have hone := GlobalTheory.T.norm_tangentDenominator_eq_one_of_unitDiscr_double g.W (xAt g P) (yAt g P) _ ha1 ha2 ha3 ha4 ha6 hΔ eP (hx P hP) hne
    (div_mul_cancel₀ _ hne) (by rw [← hdbl]; exact hx _ hS)
  rw [hη, norm_mul, norm_pow, hu, one_pow, one_mul] at hone
  have key := GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero g.abelian₂ hlat P hP.1
  have cS := hc _ (tors_laq hS.2)
  have cP := hc _ (tors_laq hP.2)
  have key' := congrArg (lamC g.lam) key
  rw [lamC_mul' _ (neg_mem dP) (pow_mem cP 4), lamC_neg' _ dP, lamC_pow' _ cP] at key'
  have hn := congrArg norm key'
  simp only [norm_mul, norm_neg, norm_pow, hone, one_mul] at hn
  change ‖cval g (2 * P)‖ = ‖cval g P‖ ^ 4 at hn
  have nP := norm_pos_iff.2 (cval_ne_zero hlat hP.1 cP)
  simp only [logc, if_neg h2, if_neg hP.1, hn, Real.log_pow]
  push_cast; ring

theorem logc_per (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) (hg : GL3Theta.At D cc δ g)
    {t ω : ℂ} (hL : InRationalLattice g.abelian₂ t) (ht : t ∉ g.abelian₂) (hω : ω ∈ g.abelian₂) : logc g (t + ω) = logc g t :=
  logc_eq_of_norm (fun h => ht (by simpa using sub_mem h hω)) ht (GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic D p cc δ g hg t ω hL hω)

theorem logc_neg (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) (hg : GL3Theta.At D cc δ g)
    {t : ℂ} (hL : InRationalLattice g.abelian₂ t) (ht : t ∉ g.abelian₂) : logc g (-t) = logc g t := by
  obtain ⟨hlat, -, -, -, hc, -⟩ := ctx D cc δ g hg
  refine logc_eq_of_norm (fun h => ht (by simpa using neg_mem h)) ht ?_
  simp only [cval]
  rw [thetaTranslateValueAtZero_neg hlat, lamC_neg' _ (hc t hL), norm_neg]

theorem half (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) (hg : GL3Theta.At D cc δ g)
    (hx : ∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖xAt g s‖ ≤ 1) (P : ℂ)
    (hP : GL3Theta.Tors1 p g.abelian₂ P) (h2 : 2 * P ∈ g.abelian₂) : logc g P = 0 := by
  obtain ⟨hlat, -⟩ := ctx D cc δ g hg
  obtain ⟨n, hn, hnp, hnP⟩ := hP.2
  have hp2 : Nat.Coprime 2 p := by
    by_contra hc
    have hp : p = 2 := by
      have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).not.1 hc
      push_neg at this
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 this).symm
    subst hp
    have hodd : ¬ 2 ∣ n := fun hd => by
      have := Nat.Coprime.coprime_dvd_left hd hnp
      norm_num at this
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    apply hP.1
    have e : P = ((2 * k + 1 : ℕ) : ℂ) * P - (k : ℂ) * (2 * P) := by push_cast; ring
    rw [e]
    exact sub_mem hnP (natmul_mem h2 k)
  have tors2 : ∀ z : ℂ, 2 * z ∈ g.abelian₂ → z ∉ g.abelian₂ → GL3Theta.Tors1 p g.abelian₂ z :=
    fun z hz hz' => ⟨hz', 2, two_pos, hp2, by exact_mod_cast hz⟩
  obtain ⟨P', h2', hP', hd⟩ := GlobalTheory.T.exists_half_period_sub_not_mem_of_isLat g.abelian₂ hlat P h2 hP.1
  set R := P - P' with hR
  have h2R : 2 * R ∈ g.abelian₂ := by rw [hR, mul_sub]; exact sub_mem h2 h2'
  have tP' := tors2 P' h2' hP'
  have tR := tors2 R h2R hd
  have hPP : P + P' = R + 2 * P' := by rw [hR]; ring
  have hPP' : P + P' ∉ g.abelian₂ := by
    rw [hPP]; exact fun h => hd (by simpa using sub_mem h h2')

  have e1 := generic D cc δ g hg hx P P' hP tP' hPP' hd
  rw [hPP, logc_per D cc δ g hg (tors_laq tR.2) hd h2'] at e1

  have hPR : P + R = -P' + 2 * P := by rw [hR]; ring
  have hPR' : P - R = P' := by rw [hR]; ring
  have hPRn : P + R ∉ g.abelian₂ := by
    rw [hPR]; exact fun h => hP' (by simpa using neg_mem (sub_mem h h2))
  have e2 := generic D cc δ g hg hx P R hP tR hPRn (by rw [hPR']; exact hP')
  rw [hPR, hPR', logc_per D cc δ g hg (tors_laq (tors_neg tP'.2)) (fun h => hP' (by simpa using neg_mem h)) h2,
    logc_neg D cc δ g hg (tors_laq tP'.2) hP'] at e2

  have hP'R : P' + R = P := by rw [hR]; ring
  have hP'R' : P' - R = -P + 2 * P' := by rw [hR]; ring
  have hP'Rn : P' - R ∉ g.abelian₂ := by
    rw [hP'R']; exact fun h => hP.1 (by simpa using neg_mem (sub_mem h h2'))
  have e3 := generic D cc δ g hg hx P' R tP' tR (by rw [hP'R]; exact hP.1) hP'Rn
  rw [hP'R, hP'R', logc_per D cc δ g hg (tors_laq (tors_neg hP.2)) (fun h => hP.1 (by simpa using neg_mem h)) h2',
    logc_neg D cc δ g hg (tors_laq hP.2) hP.1] at e3
  linarith

theorem par_holds : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g s = PowerSeries.C (GlobalTheory.ThetaTransl.cval g s) * w) →
    ∀ P Q : ℂ, (∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * P ∈ g.abelian₂) → GL3Theta.Tors1 p g.abelian₂ Q →
      GlobalTheory.ThetaTransl.logc g (P + Q) + GlobalTheory.ThetaTransl.logc g (P - Q) =
        2 * GlobalTheory.ThetaTransl.logc g P + 2 * GlobalTheory.ThetaTransl.logc g Q := by
  intro D p _ cc δ g hg hx _ P Q hP hQ
  have lQ := tors_laq hQ.2
  by_cases hPl : P ∈ g.abelian₂
  · have h1 : P + Q = Q + P := add_comm P Q
    have h2 : P - Q = -Q + P := by ring
    have hQn : -Q ∉ g.abelian₂ := fun h => hQ.1 (by simpa using neg_mem h)
    rw [h1, h2, logc_per D cc δ g hg lQ hQ.1 hPl, logc_per D cc δ g hg (tors_laq (tors_neg hQ.2)) hQn hPl,
      logc_neg D cc δ g hg lQ hQ.1]
    simp only [logc, if_pos hPl]
    ring
  have tP : GL3Theta.Tors1 p g.abelian₂ P := ⟨hPl, hP⟩
  by_cases hS : P + Q ∈ g.abelian₂ <;> by_cases hD : P - Q ∈ g.abelian₂
  ·
    have h2 : 2 * P ∈ g.abelian₂ := by
      rw [two_mul, show P + P = (P + Q) + (P - Q) by ring]; exact add_mem hS hD
    have a2 : logc g Q = logc g P := by
      rw [show Q = P + -(P - Q) by ring]; exact logc_per D cc δ g hg (tors_laq hP) hPl (neg_mem hD)
    have a3 := half D cc δ g hg hx P tP h2
    have s1 : logc g (P + Q) = 0 := by simp [logc, hS]
    have s2 : logc g (P - Q) = 0 := by simp [logc, hD]
    linarith
  ·
    have h2 : 2 * P ∉ g.abelian₂ := fun h => hD (by
      rw [show P - Q = 2 * P - (P + Q) by ring]; exact sub_mem h hS)
    have a1 : logc g (P - Q) = logc g (2 * P) := by
      rw [show P - Q = 2 * P + -(P + Q) by ring]
      exact logc_per D cc δ g hg (tors_laq (tors_two hP)) h2 (neg_mem hS)
    have a2 : logc g Q = logc g P := by
      rw [show Q = -P + (P + Q) by ring,
        logc_per D cc δ g hg (tors_laq (tors_neg hP)) (fun h => hPl (by simpa using neg_mem h)) hS]
      exact logc_neg D cc δ g hg (tors_laq hP) hPl
    have a3 := doubling D cc δ g hg hx P tP h2
    have s1 : logc g (P + Q) = 0 := by simp [logc, hS]
    linarith
  ·
    have h2 : 2 * P ∉ g.abelian₂ := fun h => hS (by
      rw [show P + Q = 2 * P - (P - Q) by ring]; exact sub_mem h hD)
    have a1 : logc g (P + Q) = logc g (2 * P) := by
      rw [show P + Q = 2 * P + -(P - Q) by ring]
      exact logc_per D cc δ g hg (tors_laq (tors_two hP)) h2 (neg_mem hD)
    have a2 : logc g Q = logc g P := by
      rw [show Q = P + -(P - Q) by ring]; exact logc_per D cc δ g hg (tors_laq hP) hPl (neg_mem hD)
    have a3 := doubling D cc δ g hg hx P tP h2
    have s2 : logc g (P - Q) = 0 := by simp [logc, hD]
    linarith
  · exact generic D cc δ g hg hx P Q tP hQ hS hD

end GlobalTheory.ThetaPar
