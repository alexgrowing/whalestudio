import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstMulLogEqNSer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEqStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.TorsionHeight

theorem setup (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) :
    IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ TaylorLogMetric.discr g.abelian₂ = 1 ∧
      (∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar ∧ wpD g.abelian₂ t ∈ Qbar) ∧
      (∀ t, InRationalLattice g.abelian₂ t → U1 g.abelian₂ t (sgStar g.abelian₂) 0 ∈ Qbar) ∧ g.Ok := by
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 huse hwp
  refine ⟨hlat, h2, h3, hdisc, hwp, fun t ht => ?_, hok⟩
  have := huse t ht 0
  simpa [coef1] using this

theorem lamC_eq {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {ι : ℂ ≃+* ℂ_[p]}
    (hι : ∀ x : Qbar, ι (x : ℂ) = lam x) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = ι x := by
  rw [lamC, dif_pos hx]; exact (hι ⟨x, hx⟩).symm

theorem model_polys {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (A B P : ℂ_[p])
    (hA : lamC g.lam (-(g2 g.abelian₂) / 4) = -A / 4) (hB : lamC g.lam (-(g3 g.abelian₂) / 4) = -B / 4) :
    4 * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 3 +
        g.W.b₂ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 2 +
        2 * g.W.b₄ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) + g.W.b₆ =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * (4 * P ^ 3 - A * P - B) ∧
    (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 4 -
        g.W.b₄ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 2 -
        2 * g.W.b₆ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) - g.W.b₈ =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 8 *
        (((P ^ 2 + A / 4) ^ 2 + 2 * B * P) - g.C.r * (4 * P ^ 3 - A * P - B)) := by
  rw [GL3Theta.G1.W, WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆, WeierstrassCurve.variableChange_b₈]
  simp only [WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, wModel, hA, hB]
  constructor <;> ring

theorem lattice_torsion_two_mul {Λ : AddSubgroup ℂ} {v : ℂ} (hv : InRationalLattice Λ v) : InRationalLattice Λ (2 * v) := by
  obtain ⟨m, hm, hmv⟩ := hv
  exact ⟨m, hm, by rw [show (m : ℂ) * (2 * v) = (m * v) + (m * v) by ring]; exact add_mem hmv hmv⟩

theorem sigmaStarTranslate_zero_ne_zero_off_lattice {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    U1 Λ v (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((h.sg_eq_zero v).not.2 hv) (Complex.exp_ne_zero _)

theorem dbl_complex {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (h2v : 2 * v ∉ Λ) :
    wpF Λ (2 * v) * (4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ) =
      (wpF Λ v ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ v := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨e2, e3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  rw [e2, e3, (hw _ h2v).1, (hw _ hv).1, two_mul]
  exact GlobalTheory.TorsionIntegral.dbl L (fun h' => hv ((hL v).2 h')) (fun h' => h2v ((hL _).2 (by rwa [two_mul])))

theorem mu_double (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) (hv0 : v ∉ g.abelian₂) (h2v : 2 * v ∉ g.abelian₂) :
    ‖GlobalTheory.ThetaTransl.cval g (2 * v)‖ ^ 2 * max 1 ‖xAt g (2 * v)‖ =
      (‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖) ^ 4 := by
  obtain ⟨hlat, h2, h3, hdisc, hwp, hU, hok⟩ := setup D p cc δ g hg
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p g.lam
  have hv2 := lattice_torsion_two_mul hv
  obtain ⟨hP, hD⟩ := hwp v hv hv0
  obtain ⟨hP2, -⟩ := hwp (2 * v) hv2 h2v
  have hdup := GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero g.abelian₂ hlat v hv0
  have hsq := GlobalTheory.ThetaPar.ModelPoint.wpD_sq hlat hv0
  have hdbl := dbl_complex hlat hv0 h2v
  obtain ⟨hε, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat h2 h3 hdisc
  obtain ⟨⟨ha1, ha2, ha3, ha4, ha6, hΔ⟩, -⟩ := hok
  have key := GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant p g.W ha1 ha2 ha3 ha4 ha6 hΔ (xAt g v)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hεdef
  have hA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(ι (g2 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h2, lamC_eq hι h2]
  have hB : lamC g.lam (-(g3 g.abelian₂) / 4) = -(ι (g3 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h3, lamC_eq hι h3]
  obtain ⟨hψ, hφ⟩ := model_polys g (ι (g2 g.abelian₂)) (ι (g3 g.abelian₂)) (ι (wpF g.abelian₂ v)) hA hB
  have hx : xAt g v = ε ^ 2 * (ι (wpF g.abelian₂ v) - g.C.r) := by
    rw [xAt, lamC_eq hι hP]
  have hx2 : xAt g (2 * v) = ε ^ 2 * (ι (wpF g.abelian₂ (2 * v)) - g.C.r) := by
    rw [xAt, lamC_eq hι hP2]
  have hc : GlobalTheory.ThetaTransl.cval g v = ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0) := by
    rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU v hv)]
  have hc2 : GlobalTheory.ThetaTransl.cval g (2 * v) = -(ι (wpD g.abelian₂ v)) * ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0) ^ 4 := by
    rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU _ hv2), hdup, map_mul, map_neg, map_pow]
  have hsqι := congrArg ι hsq
  have hdblι := congrArg ι hdbl
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_div₀] at hsqι hdblι
  rw [← hx] at hψ hφ
  set P := ι (wpF g.abelian₂ v)
  set P₂ := ι (wpF g.abelian₂ (2 * v))
  set Q := ι (wpD g.abelian₂ v)
  set c := ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0)
  set A := ι (g2 g.abelian₂)
  set B := ι (g3 g.abelian₂)
  set x := xAt g v
  set ψ := 4 * x ^ 3 + g.W.b₂ * x ^ 2 + 2 * g.W.b₄ * x + g.W.b₆
  set φ := x ^ 4 - g.W.b₄ * x ^ 2 - 2 * g.W.b₆ * x - g.W.b₈
  have hxψ : xAt g (2 * v) * ψ = φ := by
    rw [hx2, hψ, hφ]
    linear_combination ε ^ 8 * hdblι
  have hQ : ‖Q‖ ^ 2 = ‖ψ‖ := by
    rw [hψ, norm_mul, norm_pow, hε, one_pow, one_mul, ← norm_pow, hsqι]
  rw [hc2, hc, norm_mul, norm_neg, norm_pow, mul_pow, ← pow_mul, hQ, mul_pow (‖c‖ ^ 2), ← pow_mul, ← key]
  have e1 : ‖ψ‖ * max 1 ‖xAt g (2 * v)‖ = max ‖φ‖ ‖ψ‖ := by
    rw [mul_max_of_nonneg _ _ (norm_nonneg _), mul_one, ← norm_mul, mul_comm ψ, hxψ, max_comm]
  calc ‖ψ‖ * ‖c‖ ^ (4 * 2) * max 1 ‖xAt g (2 * v)‖ = ‖c‖ ^ (4 * 2) * (‖ψ‖ * max 1 ‖xAt g (2 * v)‖) := by ring
    _ = _ := by rw [e1]

theorem mu_two_tors (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) (hv0 : v ∉ g.abelian₂) (h2v : 2 * v ∈ g.abelian₂) :
    (‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖) ^ 4 = 1 := by
  obtain ⟨hlat, h2, h3, hdisc, hwp, hU, hok⟩ := setup D p cc δ g hg
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p g.lam
  obtain ⟨hP, hD⟩ := hwp v hv hv0
  have hdup := GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero g.abelian₂ hlat v hv0
  have hsq := GlobalTheory.ThetaPar.ModelPoint.wpD_sq hlat hv0
  have h8 := GlobalTheory.T.latticeTranslate_halfPeriod_sigmaStar_pow_eight_mul_eq_one g.abelian₂ hlat v hv0 h2v
  have h0 : U1 g.abelian₂ (2 * v) (sgStar g.abelian₂) 0 = 0 := by
    rw [hlat.sg_law h2v 0, (hlat.sg_eq_zero 0).2 (zero_mem _), mul_zero]
  have hD0 : wpD g.abelian₂ v = 0 := by
    rw [h0] at hdup
    have hne := pow_ne_zero 4 (sigmaStarTranslate_zero_ne_zero_off_lattice hlat hv0)
    have : wpD g.abelian₂ v * U1 g.abelian₂ v (sgStar g.abelian₂) 0 ^ 4 = 0 := by linear_combination hdup
    exact (mul_eq_zero.1 this).resolve_right hne
  have hf : 4 * wpF g.abelian₂ v ^ 3 - g2 g.abelian₂ * wpF g.abelian₂ v - g3 g.abelian₂ = 0 := by
    rw [← hsq, hD0]; ring
  obtain ⟨hε, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat h2 h3 hdisc
  obtain ⟨⟨ha1, ha2, ha3, ha4, ha6, hΔ⟩, -⟩ := hok
  have key := GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant p g.W ha1 ha2 ha3 ha4 ha6 hΔ (xAt g v)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hεdef
  have hA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(ι (g2 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h2, lamC_eq hι h2]
  have hB : lamC g.lam (-(g3 g.abelian₂) / 4) = -(ι (g3 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h3, lamC_eq hι h3]
  obtain ⟨hψ, hφ⟩ := model_polys g (ι (g2 g.abelian₂)) (ι (g3 g.abelian₂)) (ι (wpF g.abelian₂ v)) hA hB
  have hx : xAt g v = ε ^ 2 * (ι (wpF g.abelian₂ v) - g.C.r) := by
    rw [xAt, lamC_eq hι hP]
  have hc : GlobalTheory.ThetaTransl.cval g v = ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0) := by
    rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU v hv)]
  have hfι := congrArg ι hf
  have h8ι := congrArg ι h8
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_div₀, map_zero, map_one] at hfι h8ι
  rw [← hx] at hψ hφ
  rw [hfι, mul_zero] at hψ
  rw [hfι, mul_zero, sub_zero] at hφ
  rw [hψ, norm_zero, max_eq_left (norm_nonneg _), hφ] at key
  rw [hc, mul_pow, ← pow_mul, ← key, norm_mul, norm_pow, hε, one_pow, one_mul, ← norm_pow, ← norm_mul, h8ι,
    norm_one]

def mu {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ) : ℝ :=
  if v ∈ g.abelian₂ then 1 else ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖

theorem mu_add (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v ω : ℂ) (hv : InRationalLattice g.abelian₂ v) (hω : ω ∈ g.abelian₂) : mu g (v + ω) = mu g v := by
  obtain ⟨hlat, -⟩ := setup D p cc δ g hg
  by_cases hv0 : v ∈ g.abelian₂
  · rw [mu, mu, if_pos (add_mem hv0 hω), if_pos hv0]
  · have h1 : v + ω ∉ g.abelian₂ := fun h => hv0 (by simpa using sub_mem h hω)
    rw [mu, mu, if_neg h1, if_neg hv0, GlobalTheory.ThetaTransl.cval_norm_periodic D p cc δ g hg v ω hv hω]
    congr 3
    rw [xAt, xAt, hlat.wpF_add_of_mem hω]

theorem mu_two (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) : mu g (2 * v) = mu g v ^ 4 := by
  by_cases hv0 : v ∈ g.abelian₂
  · have h2 : 2 * v ∈ g.abelian₂ := by rw [two_mul]; exact add_mem hv0 hv0
    rw [mu, mu, if_pos h2, if_pos hv0, one_pow]
  by_cases h2v : 2 * v ∈ g.abelian₂
  · rw [mu, mu, if_pos h2v, if_neg hv0, mu_two_tors D p cc δ g hg v hv hv0 h2v]
  · rw [mu, mu, if_neg h2v, if_neg hv0, mu_double D p cc δ g hg v hv hv0 h2v]

theorem mu_pow_two (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) (k : ℕ) :
    mu g ((2 : ℂ) ^ k * v) = mu g v ^ (4 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : InRationalLattice g.abelian₂ ((2 : ℂ) ^ k * v) := by
      obtain ⟨m, hm, hmv⟩ := hv
      refine ⟨m, hm, ?_⟩
      rw [show (m : ℂ) * ((2 : ℂ) ^ k * v) = ((2 ^ k : ℕ) : ℤ) • ((m : ℂ) * v) by push_cast; ring]
      exact zsmul_mem hmv _
    rw [pow_succ, mul_comm ((2 : ℂ) ^ k) 2, mul_assoc, mu_two D p cc δ g hg _ hk, ih, ← pow_mul, pow_succ]

theorem mu_pos (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) : 0 < mu g v := by
  obtain ⟨hlat, -, -, -, -, hU, -⟩ := setup D p cc δ g hg
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p g.lam
  unfold mu
  split_ifs with hv0
  · exact one_pos
  · have hc : GlobalTheory.ThetaTransl.cval g v ≠ 0 := by
      rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU v hv)]
      exact (map_ne_zero ι).2 (sigmaStarTranslate_zero_ne_zero_off_lattice hlat hv0)
    exact mul_pos (pow_pos (norm_pos_iff.2 hc) 2) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem eq_one_of_pow_eq {a : ℝ} (ha : 0 < a) {m n : ℕ} (hmn : m < n) (h : a ^ m = a ^ n) : a = 1 := by
  by_contra hne
  exact hmn.ne (pow_right_injective₀ ha hne h)

theorem height_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ v : ℂ, InRationalLattice g.abelian₂ v → v ∉ g.abelian₂ →
      ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖ = 1 := by
  intro D p _ cc δ g hg v hv hv0
  obtain ⟨m, hm, hmv⟩ := hv
  have hv' : InRationalLattice g.abelian₂ v := ⟨m, hm, hmv⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (2 : ZMod m) ^ k)
  have step : ∀ a b : ℕ, a < b → (2 : ZMod m) ^ a = (2 : ZMod m) ^ b → mu g v = 1 := by
    intro a b hlt hpow
    have hdvd : (m : ℤ) ∣ 2 ^ b - 2 ^ a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hpow, sub_self]
    obtain ⟨c, hc⟩ := hdvd
    have hmem : (2 : ℂ) ^ b * v = (2 : ℂ) ^ a * v + c • ((m : ℂ) * v) := by
      have hc' : ((2 : ℂ) ^ b - 2 ^ a) = (m : ℂ) * c := by exact_mod_cast hc
      rw [zsmul_eq_mul]
      linear_combination v * hc'
    have hva : InRationalLattice g.abelian₂ ((2 : ℂ) ^ a * v) := by
      refine ⟨m, hm, ?_⟩
      rw [show (m : ℂ) * ((2 : ℂ) ^ a * v) = ((2 ^ a : ℕ) : ℤ) • ((m : ℂ) * v) by push_cast; ring]
      exact zsmul_mem hmv _
    have h1 := mu_add D p cc δ g hg _ _ hva (zsmul_mem hmv c)
    rw [← hmem, mu_pow_two D p cc δ g hg v hv', mu_pow_two D p cc δ g hg v hv'] at h1
    exact eq_one_of_pow_eq (mu_pos D p cc δ g hg v hv')
      (Nat.pow_lt_pow_right (by norm_num) hlt) h1.symm
  have h : mu g v = 1 := by
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact step a b hlt he
    · exact step b a hlt he.symm
  rwa [mu, if_neg hv0] at h

end GlobalTheory.TorsionHeight
