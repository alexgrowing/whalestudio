import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneAddPrimePowMulNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootOfUnityPadicComplexMemRangeAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisMovesFlatByUnitRootStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.ZNotRoot

theorem pow_sub_one_sub {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∃ t : R, q ^ n - 1 - (n : R) * (q - 1) = (q - 1) ^ 2 * t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨q * t + n, ?_⟩
    push_cast
    linear_combination q * ht

theorem eval_mul_sub {R : Type*} [CommRing R] (P : Polynomial R) (x q : R) :
    ∃ r : R, P.eval (q * x) - P.eval x = (q - 1) * x * (Polynomial.derivative P).eval x + (q - 1) ^ 2 * r := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨r', hr'⟩ := hQ
    refine ⟨r + r', ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add]
    linear_combination hr + hr'
  | monomial n c =>
    obtain ⟨t, ht⟩ := pow_sub_one_sub q n
    refine ⟨c * x ^ n * t, ?_⟩
    have hd : x * (Polynomial.derivative (Polynomial.monomial n c)).eval x = c * n * x ^ n := by
      rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]; push_cast; ring
    simp only [Polynomial.eval_monomial]
    linear_combination c * x ^ n * ht - (q - 1) * hd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ev_coe (bk : BK K) (Q : Polynomial (Wq l bk.a)) :
    bk.ev (Q : bk.S) = (Q.map (wA l bk.a : Wq l bk.a →+* Ainf l)).eval (WittVector.teichmuller l bk.flat) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Polynomial.coe_add, map_add, hP, hQ, Polynomial.map_add, Polynomial.eval_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
      map_mul, map_pow, bk.ev_C, bk.ev_X]
    simp

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem theta_deriv_ne (bk : BK K) : Per.θ l (bk.ev (Polynomial.derivative bk.Ep : bk.S)) ≠ 0 := by
  obtain ⟨c, A, B, h⟩ := GlobalTheory.BSP.bezout_Ep_derivative l K bk
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h2 := congrArg (fun P : Polynomial (Wq l bk.a) => Per.θ l (bk.ev (P : bk.S))) h
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, map_add, map_mul, bk.ev_C] at h2
  intro h0
  change Per.θ l (bk.ev (A : bk.S)) * Per.θ l (bk.ev bk.E) + Per.θ l (bk.ev (B : bk.S)) * Per.θ l (bk.ev _) = _ at h2
  rw [hE, h0, mul_zero, mul_zero, add_zero, map_pow, map_natCast, map_pow, map_natCast] at h2
  have h3 := congrArg (fun x : OC l => (x : ℂ_[l])) h2
  simp only [ZeroMemClass.coe_zero] at h3
  push_cast at h3
  exact pow_ne_zero c (GlobalTheory.RingBasics.p_ne_zero (p := l)) h3.symm

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

abbrev Θ (l : ℕ) [Fact l.Prime] : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l)

theorem Θ_apply (x : Ainf l) : Θ l x = ((Per.θ l x : OC l) : ℂ_[l]) := (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 x

theorem Θ_E (bk : BK K) : Θ l (bk.ev bk.E) = 0 := by
  rw [Θ_apply]
  have : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [this]; rfl

theorem Θ_flat (bk : BK K) : Θ l (WittVector.teichmuller l bk.flat) ≠ 0 := by
  rw [Θ_apply, WittVector.fontaineTheta_teichmuller, ← (GlobalTheory.BSP.BK.prime_unif l K bk).2, coe_intToOC]
  intro h
  have h1 := congrArg norm h
  rw [PadicComplex.norm_extends, norm_zero, norm_eq_zero] at h1
  apply (GlobalTheory.BSP.BK.prime_unif l K bk).1.ne_zero
  exact Subtype.ext (Subtype.ext h1)

end GlobalTheory.BKLim.ZNotRoot

open GlobalTheory.BKLim.ZNotRoot in
theorem GlobalTheory.BKLim.exists_isZ_not_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z ∧ ∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1 := by
  intro l _ K bk
  obtain ⟨τ, hτ⟩ := GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨hφ, ε, η, hε, hη⟩ := id hτ
  set u : Ainf l := WittVector.teichmuller l bk.flat with hu_def
  set D : Ainf l := bk.ev (Polynomial.derivative bk.Ep : bk.S) with hD_def
  set a : ℂ_[l] := Θ l ((↑η⁻¹ : Ainf l) * τ * u * D) with ha_def
  have ha : a ≠ 0 := by
    rw [ha_def, map_mul, map_mul, map_mul]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) (Θ_flat bk)) ?_
    · exact ((Units.isUnit η⁻¹).map (Θ l)).ne_zero
    · simpa using GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    · rw [Θ_apply]; intro h
      apply theta_deriv_ne bk
      exact Subtype.ext h
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_one_add_primePow_mul_not_rootOfUnity l a ha
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_moves_flat_by_unit_root l (GlobalTheory.T.rootOfUnity_padicComplex_mem_range_algClosure l) K bk (ε ^ (l ^ k)) (by rw [map_pow, hε.1, one_pow])
  set μ : Ainf l := WittVector.teichmuller l ε - 1 with hμ_def
  set E : Ainf l := bk.ev bk.E with hE_def
  set P : Polynomial (Ainf l) := bk.Ep.map (wA l bk.a : Wq l bk.a →+* Ainf l) with hP_def
  have hEP : E = P.eval u := ev_coe bk bk.Ep
  have hDP : D = (Polynomial.derivative P).eval u := by
    rw [hD_def, ev_coe, hP_def, Polynomial.derivative_map]
  have hσu : Per.σA (g : GQ l) u = WittVector.teichmuller l ε ^ (l ^ k) * u := by
    rw [hu_def, GlobalTheory.RingIface.sigA_teich, hg, map_mul, map_pow]
  have hσE : Per.σA (g : GQ l) E = P.eval (WittVector.teichmuller l ε ^ (l ^ k) * u) := by
    rw [hEP, hP_def, Polynomial.eval_map, Polynomial.hom_eval₂, hσu, ← Polynomial.eval_map]
    congr 2
    exact RingHom.ext fun w => bk.gal_w g w
  obtain ⟨r, hr⟩ := eval_mul_sub P u (WittVector.teichmuller l ε ^ (l ^ k))
  obtain ⟨s, hs⟩ := pow_sub_one_sub (WittVector.teichmuller l ε) (l ^ k)
  have hμE : μ = (↑η⁻¹ : Ainf l) * E * τ := by
    have h1 : (η : Ainf l) * μ = E * τ := by rw [hμ_def, ← hη, hφ]
    calc μ = (↑η⁻¹ : Ainf l) * ((η : Ainf l) * μ) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [h1]; ring
  set L : Ainf l := ((l ^ k : ℕ) : Ainf l) with hL_def
  have hq : WittVector.teichmuller l ε ^ (l ^ k) - 1 = (↑η⁻¹ : Ainf l) * E * τ * (L + μ * s) := by
    rw [← hμE, hμ_def]; linear_combination hs
  set w : Ainf l := 1 + (↑η⁻¹ : Ainf l) * τ * (L + μ * s) * u * D +
    E * ((↑η⁻¹ : Ainf l) * τ) ^ 2 * (L + μ * s) ^ 2 * r with hw_def
  have hw : Per.σA (g : GQ l) E = E * w := by
    rw [hσE, hw_def, hDP]
    rw [hq] at hr
    linear_combination hr - hEP
  have hΘw : Θ l w = 1 + (l : ℂ_[l]) ^ k * a := by
    have hΘE : Θ l E = 0 := Θ_E bk
    rw [hw_def, ha_def, hL_def, hμE]
    simp only [map_add, map_mul, map_pow, map_one, hΘE, map_natCast]
    push_cast
    ring
  refine ⟨g, (Θ l w)⁻¹, ⟨w, hw, ?_⟩, fun i hi => ?_⟩
  · change (Θ l w)⁻¹ * Θ l w = 1
    rw [hΘw]; exact inv_mul_cancel₀ hk0
  · rw [inv_pow, Ne, inv_eq_one, hΘw]
    exact hk i hi

end
