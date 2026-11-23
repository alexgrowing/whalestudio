import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsiStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadicStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaUnit
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

section
variable {p : ℕ} [Fact p.Prime]

theorem lamC_eq (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul' (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_eq lam hx, lamC_eq lam hy, lamC_eq lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) (h0 : x ≠ 0) : lamC lam x ≠ 0 := by
  rw [lamC_eq lam hx]
  intro h
  apply h0
  have := (map_eq_zero_iff lam lam.injective).1 h
  exact congrArg Subtype.val this

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  have := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 1).2 norm_one.le
  rwa [map_one] at this

theorem intSer_pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_one (p := p)
  | succ n ih => rw [pow_succ]; exact ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ ih hf).2.2

end

theorem tors_neg' {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : GL3Theta.Tors1 p Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem laQ_of_tors {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem thetaTranslateOperator_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) {t : ℂ} (ht : t ∉ Λ) :
    U1 Λ t (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((hlat.sg_eq_zero t).not.2 ht) (Complex.exp_ne_zero _)

theorem atU_smul' {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 hF).1

theorem tau_eq_C_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  intro D p _ cc δ g hg hx t ht
  have hA := GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion D p cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hsg : AlgEnt (sgStar g.abelian₂) := by
    have := halg 0 ⟨1, one_pos, by simp⟩
    rwa [thetaTranslateOperator_zero_eq_self] at this
  have hEi : (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hE]; exact one_ne_zero)
  have hcon : ∀ s, InRationalLattice g.abelian₂ s → PowerSeries.constantCoeff (tau g s) = cval g s ∧
      U1 g.abelian₂ s (sgStar g.abelian₂) 0 ∈ Qbar := by
    intro s hs
    obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ (halg s hs)
    refine ⟨?_, c⟩
    rw [tau, map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, d, cval]
  have hq := laQ_of_tors ht
  have hq' := laQ_of_tors (tors_neg' ht)
  obtain ⟨c1, c2⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t ht.1 (hwp t hq ht.1).1
  have a3 := (hcon t hq).2
  have b3 := (hcon (-t) hq').2
  have e := (atU_smul' g (mul_mem a3 b3) c1).2
  rw [funext (hlat'.sqTh_mul ht.1), ((GlobalTheory.SerTransport.transport p g).1 _ _ (halg _ hq) (halg _ hq')).1.2,
    c2, lamC_mul' _ a3 b3] at e
  have hprod : tau g t * tau g (-t) = PowerSeries.C (cval g t * cval g (-t)) *
      lineSer g.wq⁻¹ (xAt g t) := by
    simp only [tau, cval]
    linear_combination ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹) * e +
      PowerSeries.C (lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0)) *
        lineSer g.wq⁻¹ (xAt g t) * ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq + 1) * hEi

  have hL : IntSer (lineSer g.wq⁻¹ (xAt g t)) := by
    have h1 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 (xAt g t)).2 (hx t ht)
    have h2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
    have h3 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h2 h2).2.2
    have h4 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h1 h3).2.2
    have h5 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ hw h4).2.1
    simpa [lineSer, _root_.sq, mul_assoc] using h5
  obtain ⟨n, hn, hcop, hnt⟩ := ht.2
  have hnt' : (n : ℂ) * (-t) ∈ g.abelian₂ := by rw [mul_neg]; exact neg_mem hnt
  have B1 := hA t ht n hn hnt
  have B2 := hA (-t) (tors_neg' ht) n hn hnt'
  set c := cval g t with hc
  set c' := cval g (-t) with hc'
  have hc0 : c ≠ 0 := lamC_ne_zero _ a3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' ht.1)
  have hc0' : c' ≠ 0 := lamC_ne_zero _ b3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' (tors_neg' ht).1)
  have hpow : tau g t ^ n * tau g (-t) ^ n = PowerSeries.C ((c * c') ^ n) * lineSer g.wq⁻¹ (xAt g t) ^ n := by
    rw [← mul_pow, hprod, mul_pow, map_pow]
  have hbound : ∀ k, ‖PowerSeries.coeff k (tau g t ^ n * tau g (-t) ^ n)‖ ≤ ‖c * c'‖ ^ n := by
    intro k
    rw [hpow, PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (intSer_pow hL n k)
  have G := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p _ _ _ B1 B2 hbound
  have h0' : PowerSeries.coeff 0 (tau g (-t) ^ n) = c' ^ n := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, (hcon _ hq').1]
  have hcn : 0 < ‖c'‖ ^ n := pow_pos (norm_pos_iff.2 hc0') n
  have hle : ∀ i, ‖PowerSeries.coeff i (tau g t ^ n)‖ ≤ ‖c‖ ^ n := by
    intro i
    have := G i 0
    rw [h0', norm_pow, norm_mul, mul_pow] at this
    exact le_of_mul_le_mul_right this hcn
  set s := PowerSeries.C c⁻¹ * tau g t with hs
  have hsn : IntSer (s ^ n) := by
    intro k
    rw [hs, mul_pow, ← map_pow, PowerSeries.coeff_C_mul, norm_mul, norm_pow, norm_inv]
    have hcp : 0 < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc0) n
    calc ‖c‖⁻¹ ^ n * ‖PowerSeries.coeff k (tau g t ^ n)‖ ≤ ‖c‖⁻¹ ^ n * ‖c‖ ^ n :=
          mul_le_mul_of_nonneg_left (hle k) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_pow]
  have hs0 : PowerSeries.constantCoeff s = 1 := by
    rw [hs, map_mul, PowerSeries.constantCoeff_C, (hcon t hq).1, inv_mul_cancel₀ hc0]
  refine ⟨s, GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic p n hn hcop s hs0 hsn, hs0, ?_⟩
  rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end GlobalTheory.ThetaUnit
