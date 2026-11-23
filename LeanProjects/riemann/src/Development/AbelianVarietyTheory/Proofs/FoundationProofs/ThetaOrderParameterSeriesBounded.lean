import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAnalyticOfTendsto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBou
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebra
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaOrderBdd
open GlobalTheory.ThetaTransl GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

theorem ratio_add (hΛ : IsLat Λ) {G : ℂ → ℂ} {k : ℕ}
    (hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    G (z + l) / sgStar Λ (z + l) ^ k = G z / sgStar Λ z ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hlaw l hl z
  by_cases hz : z ∈ Λ
  · rw [(hΛ.sg_eq_zero z).2 hz, (hΛ.sg_eq_zero _).2 (add_mem hz hl), zero_pow hk.ne']
    simp
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have h1 : sgStar Λ (z + l) ≠ 0 := (hΛ.sg_eq_zero _).not.2 (fun h => hz (by simpa using sub_mem h hl))
  rw [div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  exact hlaw l hl z

theorem exists_decomp_gen : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (k : ℕ) (G : ℂ → ℂ), Differentiable ℂ G →
    (∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k) →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), k ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - k) * G z =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ k G hG hlaw v hv
  obtain ⟨L, h⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ := hΛ.differentiable
  have hS := hΛ.differentiable_sqTh v
  have hT : Continuous (sqThD Λ v) := by
    have h1 := hσ.deriv.continuous
    have h2 := hS.deriv.continuous
    have h3 := hσ.continuous
    have h4 := hS.continuous
    unfold sqThD
    fun_prop
  have hc : ∀ z, z ∉ L.lattice →
      ContinuousAt (fun z => G z / sgStar Λ z ^ k) z := fun z hz =>
    (hG z).continuousAt.div ((hσ z).continuousAt.pow k)
      (pow_ne_zero _ ((hΛ.sg_eq_zero z).not.2 ((h z).not.2 hz)))
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L
    (g := fun z => G z / sgStar Λ z ^ k)
    (fun a => (hG.analyticAt a).meromorphicAt.div ((hσ.analyticAt a).meromorphicAt.pow k))
    (fun a ha => ⟨_, (hc a ha).tendsto.mono_left nhdsWithin_le_nhds⟩)
    (fun z l hl => ratio_add hΛ hlaw z ((h l).2 hl))
  have hAB' : ∀ z, z ∉ L.lattice → G z / sgStar Λ z ^ k =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hz
    have h1 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
    have h2 := (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    have h3 : ContinuousAt (fun z => A.eval (L.weierstrassP z) +
        B.eval (L.weierstrassP z) * L.derivWeierstrassP z) z :=
      (A.continuous.continuousAt.comp h1).add ((B.continuous.continuousAt.comp h1).mul h2)
    exact tendsto_nhds_unique_of_eventuallyEq ((hc z hz).tendsto.mono_left nhdsWithin_le_nhds)
      (h3.tendsto.mono_left nhdsWithin_le_nhds) (hAB z)
  set A' := Polynomial.taylor (wpF Λ v) A with hA'
  set B' := Polynomial.taylor (wpF Λ v) B with hB'
  obtain ⟨I, hI⟩ : ∃ I, I = A'.natDegree + B'.natDegree + k := ⟨_, rfl⟩
  refine ⟨I, A'.coeff, B'.coeff, by omega, fun z => ?_⟩
  have h3 := hσ.continuous
  have h4 := hS.continuous
  have h5 := hG.continuous
  refine congrFun (Continuous.ext_on hΛ.dense_compl
    (f := fun z => sgStar Λ z ^ (2 * I + 3 - k) * G z)
    (g := fun z => ∑ i ∈ Finset.range (I + 1),
      A'.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
      ∑ j ∈ Finset.range (I + 1),
        B'.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z))
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have hz' : z ∉ L.lattice := (h z).not.1 hz
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have e := hAB' z hz'
  rw [← Polynomial.taylor_eval_sub (wpF Λ v) A, ← Polynomial.taylor_eval_sub (wpF Λ v) B,
    ← hA', ← hB', Polynomial.eval_eq_sum_range' (n := I + 1) (p := A') (by omega),
    Polynomial.eval_eq_sum_range' (n := I + 1) (p := B') (by omega),
    div_eq_iff (pow_ne_zero _ h0)] at e
  beta_reduce
  rw [e, mul_left_comm, ← pow_add, Nat.sub_add_cancel (by omega), sqThD_eq hΛ L h hv hz,
    hΛ.sqTh_eq hv hz, GlobalTheory.OddTheta.wpF_eq L Λ h z, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_
  all_goals
    obtain ⟨m, rfl⟩ : ∃ m, I = i + m := Nat.exists_eq_add_of_le (by simpa [Nat.lt_succ_iff] using hi)
    rw [Nat.add_sub_cancel_left, mul_pow]
    ring

set_option maxHeartbeats 800000 in

theorem order_bdd : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
    ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G →
      (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) →
      ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  intro p _ g hok hlat' h2 h3 hdisc hsg v hv hwv k G hG hlaw
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg v hv hwv
  have gS : GoodAt g 2 (sqTh g.abelian₂ v) := ⟨hSa, lineSer g.wq⁻¹ (xAt g v),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.ThetaTransl.CubeSer.sqThD_atU p g hok hlat' h2 h3 hdisc hsg v hv hwv
  have gT : GoodAt g 3 (sqThD g.abelian₂ v) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := exists_decomp_gen g.abelian₂ hlat' k G hG.1 hlaw v hv
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ v z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ v z ^ (j : ℕ) * sqThD g.abelian₂ v z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hG (2 * I + 3 - k) 1
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - k) * G z ^ 1 = ∑ j, c j * φ j z := by
    intro z
    rw [pow_one, hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.TranslLin.transl_lin p g _ φ c _ hEa (fun j => (gφ j).1) hEq
  choose B hB hBe using fun j => (gφ j).2
  have hS : BddSer (∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j) :=
    bdd_sum _ _ fun j _ => bdd_mul (bdd_C _) (hB j)
  rw [hEe, hsgU, pow_one] at hlin
  simp only [hBe] at hlin
  set Bk : PowerSeries ℂ_[p] := (e ^ k)⁻¹ * g.atU G with hBk
  have hGe : g.atU G = e ^ k * Bk := by
    rw [hBk, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [map_pow, he0, one_pow]; exact one_ne_zero),
      one_mul]
  rw [hGe] at hlin
  set K := 2 * I + 3 - k with hKd
  have hK : K + k = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ j, PowerSeries.C (lamC g.lam (a' j)) * (e ^ (2 * I + 3) * B j) =
      e ^ (2 * I + 3) * ∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e ^ k * Bk) =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * Bk)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨Bk, ⟨C0, fun n => ?_⟩, hGe⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaOrderBdd
