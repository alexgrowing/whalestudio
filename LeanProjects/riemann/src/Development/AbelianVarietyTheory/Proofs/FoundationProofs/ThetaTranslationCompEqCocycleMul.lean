import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormJetExpNegMulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaParam

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem integral_iff (F : PowerSeries ℂ_[p]) : IntegralMv F ↔ ∀ n, ‖coeff n F‖ ≤ 1 := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h α
    have := h (α ())
    rw [Finsupp.unique_single α]
    exact this

theorem integral_mul {F G : PowerSeries ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  rw [integral_iff] at *
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hF _) (norm_nonneg _) (hG _)

theorem integral_C {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) : IntegralMv (C c : PowerSeries ℂ_[p]) := by
  rw [integral_iff]
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem integral_X : IntegralMv (X : PowerSeries ℂ_[p]) := by
  rw [integral_iff]
  intro n
  rw [coeff_X]
  split_ifs <;> simp

theorem integral_zero : IntegralMv (0 : PowerSeries ℂ_[p]) := by
  rw [integral_iff]
  simp

theorem integral_of_mul_eq_one {E F : PowerSeries ℂ_[p]} (hE : IntegralMv E)
    (h0 : constantCoeff E = 1) (h : E * F = 1) : IntegralMv F := by
  rw [integral_iff] at *
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e := congrArg (coeff n) h
    cases n with
    | zero =>
      simp [h0] at e
      simp [e]
    | succ n =>
      rw [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons, coeff_one,
        if_neg (Nat.succ_ne_zero n)] at e
      simp only [coeff_zero_eq_constantCoeff, h0, one_mul] at e
      rw [eq_neg_of_add_eq_zero_left e, norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      have : y.1 + y.2 = n := by simpa using hy
      rw [norm_mul]
      exact mul_le_one₀ (hE _) (norm_nonneg _) (ih _ (by simp; omega))

theorem expMv_eq (F : PowerSeries ℂ_[p]) : expMv F = expPS F := by
  apply PowerSeries.ext
  intro n
  rw [expPS, coeff_mk]
  show expMv F (Finsupp.single () n) = _
  rw [expMv, Finsupp.sum_single_index rfl]
  rfl

theorem logMv_eq (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1) :
    GL3Theta.logMv F = PowerSeries.logOf F := by
  have h1 : constantCoeff (F - 1) = 0 := by simp [hF]
  apply PowerSeries.ext
  intro n
  rw [logOf_eq, PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' h1),
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · show GL3Theta.logMv F (Finsupp.single () n) = _
    rw [GL3Theta.logMv, Finsupp.sum_single_index rfl]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_log]
    split_ifs
    · simp
    · change (-1) ^ (k + 1) * coeff n ((F - 1) ^ k) / _ = _
      simp
      ring
  · intro k hk
    by_contra h
    apply hk
    have hlt : n < k := by simpa using h
    have h0 : coeff n ((F - 1) ^ k) = 0 := by
      have : (X : PowerSeries ℂ_[p]) ^ k ∣ (F - 1) ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.2 h1) k
      exact X_pow_dvd_iff.1 this n hlt
    simp [h0]

theorem mul_derivative_logOf (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1) :
    F * d⁄dX ℂ_[p] (logOf F) = d⁄dX ℂ_[p] F := by
  have h1 : constantCoeff (F - 1) = 0 := by simp [hF]
  have hs := HasSubst.of_constantCoeff_zero' h1
  have e : (1 + X) * d⁄dX ℂ_[p] (PowerSeries.log ℂ_[p]) = 1 := by
    rw [deriv_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, coeff_succ_X_mul, coeff_one, pow_succ]
  have e2 := congrArg (substAlgHom (R := ℂ_[p]) hs) e
  rw [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] at e2
  rw [logOf_eq, derivative_subst hs, ← mul_assoc]
  have e3 : F * subst (F - 1) (d⁄dX ℂ_[p] (PowerSeries.log ℂ_[p])) = 1 := by
    rwa [add_sub_cancel] at e2
  rw [e3]
  simp

theorem constantCoeff_expPS (F : PowerSeries ℂ_[p]) : constantCoeff (expPS F) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, expPS, coeff_mk]
  simp

theorem exp_neg_log_mul (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1) :
    expPS (-logOf F) * F = 1 := by
  have h0 : constantCoeff (-logOf F) = 0 := by simp [constantCoeff_logOf hF]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, GlobalTheory.ExpJets.derivative_expPS _ h0, map_neg, derivative_one]
    simp only [smul_eq_mul]
    linear_combination (-expPS (-logOf F)) * mul_derivative_logOf F hF
  · simp [hF, constantCoeff_expPS]

theorem integral_of_simeq (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1)
    (h : GL3Theta.Simeq (-GL3Theta.logMv F : MvPowerSeries Unit ℂ_[p]) 0) : IntegralMv F := by
  have h2 := h.2
  rw [sub_zero, logMv_eq F hF] at h2
  have h3 : IntegralMv (expPS (-logOf F)) := by rw [← expMv_eq]; exact h2
  refine integral_of_mul_eq_one h3 (constantCoeff_expPS _) (exp_neg_log_mul F hF)

theorem constantCoeff_subst' {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    constantCoeff (f.subst a : PowerSeries ℂ_[p]) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

theorem coeff_one_subst' {a : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    coeff 1 (f.subst a : PowerSeries ℂ_[p]) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, constantCoeff_subst' ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

theorem lamC_mul (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  simp only [lamC, dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy)]
  rw [← map_mul]; rfl

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  simp only [lamC, dif_pos (one_mem Qbar)]
  exact map_one lam

theorem lamC_zero (lam : Qbar →+* ℂ_[p]) : lamC lam 0 = 0 := by
  simp only [lamC, dif_pos (zero_mem Qbar)]
  exact map_zero lam

theorem root_mem {ζ : ℂ} {m : ℕ} (hm : 0 < m) (h : ζ ^ m = 1) : ζ ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact IsAlgebraic.of_pow hm (h ▸ isAlgebraic_one)

theorem norm_lamC_root (lam : Qbar →+* ℂ_[p]) {ζ : ℂ} {m : ℕ} (hm : 0 < m) (h : ζ ^ m = 1) :
    ‖lamC lam ζ‖ = 1 := by
  have hζ := root_mem hm h
  have e : (⟨ζ, hζ⟩ : Qbar) ^ m = 1 := Subtype.ext (by simpa using h)
  have e2 : ‖lam ⟨ζ, hζ⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
  simp only [lamC, dif_pos hζ]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2

theorem norm_lamC_inv (lam : Qbar →+* ℂ_[p]) {c : ℂ} (hc : c ∈ Qbar) (h : ‖lamC lam c‖ = 1) :
    ‖lamC lam c⁻¹‖ = 1 := by
  have h0 : c ≠ 0 := by
    rintro rfl
    simp [lamC_zero] at h
  have e := lamC_mul lam hc (inv_mem hc)
  rw [mul_inv_cancel₀ h0, lamC_one] at e
  have e2 := congrArg norm e
  rw [norm_one, norm_mul, h, one_mul] at e2
  exact e2.symm

theorem constantCoeff_arg (g : GL3Theta.G1 p) :
    constantCoeff (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * g.l) = 0 := by
  rw [map_mul]
  have : constantCoeff g.l = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, GL3Theta.G1.l, flog, coeff_mk, if_pos rfl]
  rw [this, mul_zero]

theorem constantCoeff_atU (g : GL3Theta.G1 p) (G : ℂ → ℂ) :
    constantCoeff (g.atU G) = lamC g.lam (G 0) := by
  rw [GL3Theta.G1.atU, constantCoeff_subst' (constantCoeff_arg g), ← coeff_zero_eq_constantCoeff_apply,
    GL3Theta.ser1, coeff_mk]
  simp

theorem atU_const_mul (g : GL3Theta.G1 p) {c : ℂ} (hc : c ∈ Qbar) {G : ℂ → ℂ}
    (hG : ∀ n, coef1 G n ∈ Qbar) :
    g.atU (fun z => c * G z) = C (lamC g.lam c) * g.atU G := by
  have e : GL3Theta.ser1 g.lam (fun z => c * G z) = lamC g.lam c • GL3Theta.ser1 g.lam G := by
    ext n
    simp only [GL3Theta.ser1, coeff_mk, map_smul, smul_eq_mul]
    rw [iteratedDeriv_const_mul_field, mul_div_assoc]
    exact lamC_mul g.lam hc (hG n)
  rw [GL3Theta.G1.atU, e, subst_smul (HasSubst.of_constantCoeff_zero' (constantCoeff_arg g)),
    smul_eq_C_mul]
  rfl

theorem atU_zero (g : GL3Theta.G1 p) : g.atU (fun _ => 0) = 0 := by
  have e := atU_const_mul g (c := 0) (zero_mem _) (G := fun _ => 0) (fun n => by simp [coef1])
  simpa [lamC_zero] using e

theorem atU_sg (g : GL3Theta.G1 p) (h0 : sgStar g.abelian₂ 0 = 0) :
    g.atU (sgStar g.abelian₂) =
      C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  ext n
  cases n with
  | zero => simp [constantCoeff_atU, h0, lamC_zero]
  | succ n =>
    rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul, ePhi1, coeff_mk, ← mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    rfl

theorem constantCoeff_ePhi1 (g : GL3Theta.G1 p) (hw : IsWq g.W g.wq) (h1 : deriv (sgStar g.abelian₂) 0 = 1) :
    constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 := by
  have hw0 : constantCoeff g.wq = 1 := by
    have := congrArg constantCoeff hw
    simpa using this
  have hl : coeff 1 g.l = 1 := by
    rw [GL3Theta.G1.l, flog, coeff_mk, if_neg one_ne_zero]
    simp [omegaW, hw0, PowerSeries.constantCoeff_inv, map_ofNat]
  rw [← coeff_zero_eq_constantCoeff_apply, ePhi1, coeff_mk]
  have e := coeff_one_subst' (constantCoeff_arg g) (sgSer g.lam g.abelian₂)
  have e1 : coeff 1 (sgSer g.lam g.abelian₂) = 1 := by
    simp [sgSer, h1, lamC_one]
  rw [e1, one_mul, PowerSeries.algebraMap_apply, coeff_C_mul, hl, mul_one] at e
  have e2 : coeff (0 + 1) (subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) *
      flog (g.C • wModel g.lam g.abelian₂) g.wq) (sgSer g.lam g.abelian₂) : PowerSeries ℂ_[p]) =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) := e
  rw [e2, inv_mul_cancel₀ (Units.ne_zero _)]

noncomputable def cocy (Λ : AddSubgroup ℂ) (y t : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) y - y * (starRingEnd ℂ) t) / (2 * (area Λ : ℂ)))

theorem thetaTranslation_comp_eq_cocycle_mul (Λ : AddSubgroup ℂ) (y t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ y (U1 Λ t G) z = cocy Λ y t * U1 Λ (y + t) G z := by
  simp only [U1, cocy]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  rw [map_add]
  ring

theorem thetaTranslation_const_mul (Λ : AddSubgroup ℂ) (y c : ℂ) (G : ℂ → ℂ) :
    U1 Λ y (fun z => c * G z) = fun z => c * U1 Λ y G z := by
  funext z
  simp only [U1]
  ring

theorem thetaTranslation_zero (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : U1 Λ 0 G = G := by
  funext z
  simp [U1]

theorem cocy_pow (Λ : AddSubgroup ℂ) (y t : ℂ) (m n : ℕ) :
    cocy Λ (m * y) (n * t) = cocy Λ y t ^ (m * n) := by
  simp only [cocy]
  rw [← Complex.exp_nat_mul]
  congr 1
  simp only [map_mul, map_natCast]
  push_cast
  ring

theorem cocy_ne_zero (Λ : AddSubgroup ℂ) (y t : ℂ) : cocy Λ y t ≠ 0 := Complex.exp_ne_zero _

theorem cocy_sq {Λ : AddSubgroup ℂ} {G : ℂ → ℂ} (hG : ∃ z, G z ≠ 0)
    (h : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z)
    {a b : ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) : cocy Λ a b ^ 2 = 1 := by
  obtain ⟨z, hz⟩ := hG
  have e := thetaTranslation_comp_eq_cocycle_mul Λ a b G z
  rw [show U1 Λ b G = fun z => (if b / 2 ∈ Λ then 1 else -1) * G z from funext (h b hb),
    thetaTranslation_const_mul, h _ (add_mem ha hb)] at e
  simp only [h a ha] at e
  rw [← mul_assoc, ← mul_assoc] at e
  have e2 := congrArg (· ^ 2) (mul_right_cancel₀ hz e)
  simp only [mul_pow] at e2
  split_ifs at e2 <;> simpa using e2.symm

theorem cocy_root {Λ : AddSubgroup ℂ} {G : ℂ → ℂ} (hG : ∃ z, G z ≠ 0)
    (h : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z)
    {a b : ℂ} {m n : ℕ} (ha : (m : ℂ) * a ∈ Λ) (hb : (n : ℂ) * b ∈ Λ) :
    cocy Λ a b ^ (m * n * 2) = 1 := by
  rw [pow_mul, ← cocy_pow, cocy_sq hG h ha hb]

theorem root_mul {a b : ℂ} {m n : ℕ} (ha : a ^ m = 1) (hb : b ^ n = 1) : (a * b) ^ (m * n) = 1 := by
  rw [mul_pow, pow_mul, ha, mul_comm m, pow_mul, hb]
  simp

theorem theta_param_integral : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D g.abelian₂ t0 → (p ≠ 2 → IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (GL3Theta.th0 g.abelian₂ t0)) ∧ ∀ (y : ℂ) (N : ℕ), Nat.Coprime N p → (N : ℂ) * y ∈ g.abelian₂ → IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)))) ∧ ((p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → IntegralMv (g.atU (GL3Theta.th0 g.abelian₂ t0)) ∧ ∀ (y : ℂ) (N : ℕ), Nat.Coprime N p → (N : ℂ) * y ∈ g.abelian₂ → IntegralMv (g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)))) := by
  intro D hI p hp cc δ g hAt t0 hT
  have hCrv : Crv D cc δ := ⟨hAt.1, hAt.2.2.1⟩
  have hL : g.abelian₂ = lamOf D cc δ := hAt.2.2.2.1
  have hOk := hAt.2.2.2.2
  obtain ⟨⟨-, hd, hodd, hq⟩, -⟩ :=
    GlobalTheory.OddTheta.sgStar_laws g.abelian₂ (hL ▸ (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1)
  have halg : ∀ x, InRationalLattice g.abelian₂ x → ∀ n, coef1 (U1 g.abelian₂ x (sgStar g.abelian₂)) n ∈ Qbar :=
    hL ▸ (hI.use1 cc δ hCrv).1
  have halg0 : ∀ n, coef1 (GL3Theta.th0 g.abelian₂ t0) n ∈ Qbar := by
    have := (hI.use1 cc δ hCrv).2.1
    rw [← hL] at this
    exact this t0 hT
  have hs0 : sgStar g.abelian₂ 0 = 0 := by
    have := hodd 0
    rw [neg_zero] at this
    linear_combination this / 2
  have hne : ∃ z, sgStar g.abelian₂ z ≠ 0 := by
    by_contra h
    push Not at h
    rw [show sgStar g.abelian₂ = fun _ => 0 from funext h] at hd
    simp at hd
  have hN0 : ∀ N : ℕ, Nat.Coprime N p → 0 < N := by
    intro N hN
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exact absurd (Nat.coprime_zero_left p |>.1 hN) hp.out.ne_one
    · exact h
  have h2 : ((2 : ℕ) : ℂ) * t0 ∈ g.abelian₂ := by simpa using hT.1
  by_cases hc : U1 g.abelian₂ t0 (sgStar g.abelian₂) 0 = 0
  · have e : GL3Theta.th0 g.abelian₂ t0 = fun _ => 0 := by
      funext z
      simp [GL3Theta.th0, hc]
    have e2 : ∀ y, U1 g.abelian₂ y (fun _ => 0) = fun _ => 0 := by
      intro y
      funext z
      simp [U1]
    simp only [e, e2, atU_zero, mul_zero]
    exact ⟨fun _ => ⟨integral_zero, fun _ _ _ _ => integral_zero⟩,
      fun _ => ⟨integral_zero, fun _ _ _ _ => integral_zero⟩⟩
  have ht : t0 ∉ g.abelian₂ := fun h => hc (by rw [hq t0 h, hs0, mul_zero])
  set c := U1 g.abelian₂ t0 (sgStar g.abelian₂) 0 with hcdef
  have hcQ : c ∈ Qbar := by
    have := halg t0 ⟨2, two_pos, h2⟩ 0
    simpa [coef1] using this
  have hth : GL3Theta.th0 g.abelian₂ t0 = fun z => c⁻¹ * U1 g.abelian₂ t0 (sgStar g.abelian₂) z := by
    funext z
    rw [GL3Theta.th0, div_eq_inv_mul]
  have hU : ∀ y, U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0) =
      fun z => (c⁻¹ * cocy g.abelian₂ y t0) * U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) z := by
    intro y
    rw [hth, thetaTranslation_const_mul]
    funext z
    rw [thetaTranslation_comp_eq_cocycle_mul, mul_assoc]
  have he := constantCoeff_ePhi1 g hOk.2.1 hd
  have hinv : (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [he]; exact one_ne_zero)
  have key : p ≠ 2 → ∀ (y : ℂ) (N : ℕ), Nat.Coprime N p → (N : ℂ) * y ∈ g.abelian₂ →
      IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0))) := by
    intro hp2 y N hN hy
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).2 hp2.symm
    have hcn : ‖lamC g.lam c‖ = 1 := by
      have := (hI.transl p cc δ g hAt t0 ⟨ht, 2, two_pos, hcop, h2⟩).2
      rwa [constantCoeff_atU] at this
    have hm : 0 < N * 2 * 2 := by have := hN0 N hN; positivity
    have hr := cocy_root hne hq hy h2
    have hsum : ((N * 2 : ℕ) : ℂ) * (y + t0) ∈ g.abelian₂ := by
      have := add_mem (nsmul_mem hy 2) (nsmul_mem h2 N)
      convert this using 1
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have hN2 : 0 < N * 2 := by have := hN0 N hN; positivity
    rw [hU, atU_const_mul g (mul_mem (inv_mem hcQ) (root_mem hm hr)) (halg _ ⟨_, hN2, hsum⟩),
      mul_left_comm]
    refine integral_mul (integral_C ?_) ?_
    · rw [lamC_mul _ (inv_mem hcQ) (root_mem hm hr), norm_mul, norm_lamC_inv _ hcQ hcn,
        norm_lamC_root _ hm hr, one_mul]
    · by_cases hyt : y + t0 ∈ g.abelian₂
      · have hsa : ∀ n, coef1 (sgStar g.abelian₂) n ∈ Qbar := by
          have := halg 0 ⟨1, one_pos, by simp⟩
          rwa [thetaTranslation_zero] at this
        have hsg : (if (y + t0) / 2 ∈ g.abelian₂ then (1 : ℂ) else -1) ^ 2 = 1 := by
          split_ifs <;> simp
        have hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 :=
          (hI.model p g.lam cc δ hAt.1 hAt.2.1 hAt.2.2.1).2.2 g.C (hL ▸ hOk.1)
        rw [show U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) = _ from funext (hq _ hyt),
          atU_const_mul g (root_mem two_pos hsg) hsa, atU_sg g hs0, mul_left_comm,
          mul_left_comm (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹, hinv, mul_one]
        refine integral_mul (integral_C (norm_lamC_root _ two_pos hsg).le)
          (integral_mul (integral_C ?_) integral_X)
        rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
      · exact (hI.transl p cc δ g hAt _ ⟨hyt, N * 2, hN2, Nat.Coprime.mul_left hN hcop, hsum⟩).1
  have key2 : (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → ∀ (y : ℂ) (N : ℕ), Nat.Coprime N p →
      (N : ℂ) * y ∈ g.abelian₂ → IntegralMv (g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0))) := by
    intro hsp y N hN hy
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨h1, h3⟩ := hI.two cc δ g hAt t0 hT
      by_cases hyL : y ∈ g.abelian₂
      · have h0 : IntegralMv (g.atU (GL3Theta.th0 g.abelian₂ t0)) := by
          refine integral_of_simeq _ ?_ h1
          rw [constantCoeff_atU, GL3Theta.th0, div_self hc, lamC_one]
        have hy1 : ((1 : ℕ) : ℂ) * y ∈ g.abelian₂ := by simpa using hyL
        have hsg : (if y / 2 ∈ g.abelian₂ then (1 : ℂ) else -1) ^ 2 = 1 := by
          split_ifs <;> simp
        have hr1 := cocy_root hne hq hy1 h2
        have hr2 : (cocy g.abelian₂ t0 y)⁻¹ ^ (2 * 1 * 2) = 1 := by
          rw [inv_pow, cocy_root hne hq h2 hy1, inv_one]
        have hr := root_mul (root_mul hr1 hr2) hsg
        have e : U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0) = fun z =>
            (cocy g.abelian₂ y t0 * (cocy g.abelian₂ t0 y)⁻¹ * (if y / 2 ∈ g.abelian₂ then (1 : ℂ) else -1)) *
              GL3Theta.th0 g.abelian₂ t0 z := by
          rw [hU, hth]
          funext z
          have e1 := thetaTranslation_comp_eq_cocycle_mul g.abelian₂ t0 y (sgStar g.abelian₂) z
          rw [show U1 g.abelian₂ y (sgStar g.abelian₂) = _ from funext (hq _ hyL), thetaTranslation_const_mul,
            add_comm t0] at e1
          have e0 := mul_inv_cancel₀ (cocy_ne_zero g.abelian₂ t0 y)
          simp only at e1 ⊢
          linear_combination (-(c⁻¹ * cocy g.abelian₂ y t0 * (cocy g.abelian₂ t0 y)⁻¹)) * e1 -
            (c⁻¹ * cocy g.abelian₂ y t0 * U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) z) * e0
        rw [e, atU_const_mul g (root_mem (by norm_num) hr) halg0]
        exact integral_mul (integral_C (norm_lamC_root _ (by norm_num) hr).le) h0
      · exact (h3 y ⟨hyL, N, hN0 N hN, hN, hy⟩).1
    · have h1 := (hI.split p cc δ g hAt hp2 (hsp.resolve_left hp2)).2
      have e : (g.phAt (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.ph := X_subst g.ph
      rw [e] at h1
      have h3 := integral_mul (integral_of_simeq _ he h1) (key hp2 y N hN hy)
      rwa [← mul_assoc, mul_comm (ePhi1 _ _ _ _), hinv, one_mul] at h3
  refine ⟨fun h => ⟨?_, key h⟩, fun h => ⟨?_, key2 h⟩⟩
  · have := key h 0 1 (Nat.coprime_one_left p) (by simp)
    rwa [thetaTranslation_zero] at this
  · have := key2 h 0 1 (Nat.coprime_one_left p) (by simp)
    rwa [thetaTranslation_zero] at this

end GlobalTheory.ThetaParam
