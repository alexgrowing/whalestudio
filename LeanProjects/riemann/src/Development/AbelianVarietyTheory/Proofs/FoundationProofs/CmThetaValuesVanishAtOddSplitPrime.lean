import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLawsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSplit

theorem exists_sqrt_padic {p : ℕ} [hp : Fact p.Prime] (h2 : p ≠ 2) {a : ℤ} (h : jacobiSym a p = 1) :
    ∃ z : ℤ_[p], z ^ 2 = (a : ℤ_[p]) ∧ IsUnit (2 * z) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have ha : (a : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p a).2 h0] at h
    exact zero_ne_one h
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p ha).1 h
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  have hr0 : (r : ZMod p) ≠ 0 := fun h0 => ha (by rw [hr, h0, mul_zero])
  have h20 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have : p ∣ 2 := by exact_mod_cast hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hn : ‖((2 * r : ℤ) : ℤ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at hlt
    push_cast at hlt h20
    exact mul_ne_zero h20 hr0 hlt
  have hlt : ‖((r ^ 2 - a : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr]; ring
  have e1 : ∀ z : ℤ_[p], Polynomial.aeval z (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ) = z ^ 2 - a := by
    intro z; simp
  have e2 : ∀ z : ℤ_[p], Polynomial.aeval z
      (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ)) = 2 * z := by
    intro z; simp [map_ofNat]
  obtain ⟨z, hz, -, hz', -⟩ := hensels_lemma (p := p) (F := (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℤ))
    (a := (r : ℤ_[p])) (by
      rw [e1, e2]
      push_cast at hn hlt
      rw [hn]; simpa using hlt)
  rw [e1] at hz
  rw [e2, e2] at hz'
  push_cast at hn
  exact ⟨z, sub_eq_zero.1 hz, PadicInt.isUnit_iff.2 (hz'.trans hn)⟩

theorem exists_emb (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    ∃ ψ : D.host.E →+* ℂ_[p], ∀ x, lamC lam (D.host.φ₀ x) = ψ x := by
  have hm : ∀ x, D.host.φ₀ x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom
  refine ⟨lam.comp (D.host.φ₀.codRestrict Qbar hm), fun x => ?_⟩
  simp only [lamC, dif_pos (hm x)]
  rfl

theorem exists_sqrt_host (D : D7) : ∃ b : 𝓞 D.host.K, ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) ∧
    D.host.conj ((b : D.host.K) : D.host.E) = -((b : D.host.K) : D.host.E) := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hK : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hi : IsIntegral ℤ (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) := by
    refine IsIntegral.of_pow two_pos ?_
    have : (⟨D.host.sqrtMinusD, hK⟩ : D.host.K) ^ 2 = algebraMap ℤ D.host.K (-(D.host.d : ℤ)) := by
      apply Subtype.ext
      simpa using hb
    rw [this]; exact isIntegral_algebraMap
  exact ⟨⟨_, hi⟩, hb, D.host.conj_sqd⟩

theorem idem_mem (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (h2 : p ≠ 2)
    (hs : GL3Theta.SplitK D p) : ((1, 0) : ℂ_[p] × ℂ_[p]) ∈ GL3Theta.OKp D lam := by
  obtain ⟨ψ, hψ⟩ := exists_emb D lam
  obtain ⟨b, hb, hc⟩ := exists_sqrt_host D
  let ι : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have hι : Continuous ι := (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val
  set s := ψ ((b : D.host.K) : D.host.E) with hsdef
  have hs2 : s ^ 2 = -(D.host.d : ℂ_[p]) := by rw [hsdef, ← map_pow, hb]; simp
  obtain ⟨z, hz, hu⟩ : ∃ z : ℤ_[p], ι z = s ∧ IsUnit (2 * z) := by
    obtain ⟨z, hz, hu⟩ := exists_sqrt_padic h2 hs
    have : ι z ^ 2 = s ^ 2 := by rw [← map_pow, hz, hs2]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · exact ⟨z, h, hu⟩
    · exact ⟨-z, by rw [map_neg, h, neg_neg], by simpa using hu.neg⟩
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  let f : ℤ_[p] × ℤ_[p] → ℂ_[p] × ℂ_[p] := fun x => (ι x.1 + ι x.2 * s, ι x.1 - ι x.2 * s)
  have hf : Continuous f := by fun_prop
  have hd : DenseRange (Prod.map (Int.cast : ℤ → ℤ_[p]) (Int.cast : ℤ → ℤ_[p])) :=
    PadicInt.denseRange_intCast.prodMap PadicInt.denseRange_intCast
  have hw' : 2 * s * ι w = 1 := by
    have := congrArg ι hw
    rwa [map_mul, map_mul, map_ofNat, hz, map_one] at this
  have h1 : f (z * w, w) = (1, 0) := by
    simp only [f, map_mul, hz]
    ext
    · linear_combination hw'
    · simp only; ring
  rw [← h1]
  refine map_mem_closure hf (hd (z * w, w)) ?_
  rintro _ ⟨⟨m, n⟩, rfl⟩
  refine ⟨(m : 𝓞 D.host.K) + n * b, ?_⟩
  simp only [GL3Theta.tauK, GL3Theta.tauKc, hψ, f, Prod.map]
  simp [hc, hsdef, sub_eq_add_neg]

section Series
variable {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem const_ph : PowerSeries.constantCoeff g.ph = 0 := by
  simp only [GL3Theta.G1.ph, map_neg, neg_eq_zero]
  show GL3Theta.logMv _ 0 = 0
  simp [GL3Theta.logMv]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem be_zero (h : g.Ok) (i : σ) : g.be (GL3Theta.Xv i) 0 = 0 := by
  have h1 : g.lg (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_l g)
  have h2 : g.phAt (0 : MvPowerSeries σ ℂ_[p]) = 0 := subst_zero (const_ph g)
  rw [GL3Theta.G1.be, GL3Theta.G1.add, h1, add_zero, pt_lg g h (MvPowerSeries.constantCoeff_X i), h2]
  simp

end Series

theorem splitZero : ∀ D : D7, GL3Theta.splitZero D := by
  intro D p _ cc δ g hg h2 hs
  obtain ⟨-, hN, hC⟩ := GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D
  have hα := idem_mem D g.lam h2 hs
  have hok : g.Ok := hg.2.2.2.2
  have h1 := hC p cc δ g hg h2 _ hα
  have h3 := hN p cc δ g hg h2 _ hα
  simp only [mulBy_one g hok, mulBy_zero g hok, be_zero g hok, mul_zero, map_zero, zero_mul] at h1 h3
  exact ⟨h1, h3⟩

end GlobalTheory.ThetaSplit
