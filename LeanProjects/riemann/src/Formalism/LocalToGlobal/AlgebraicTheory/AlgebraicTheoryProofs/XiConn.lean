import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.NormLtOne
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SubstSingleVar
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.GramFrameCompositionMvExpFact
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.IntOpTwoFreeOf

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsPosDef IsLat IsReps imgLat Th alphaQ opU taylorMv
  dualLat linSubst relIdx)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.CM (omegaK)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace XiConnection

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem herm_smul' (H : Sesq V) (s : ℂ) (hs : s * conj s = 1) (x y : V) : H (s • x) (s • y) = H x y := by
  rw [LinearMap.map_smulₛₗ (H (s • x)), map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  linear_combination (H x y) * hs

theorem opU_smul_iso (H : Sesq V) (s : ℂ) (hs : s * conj s = 1) (G : V → ℂ) (t z : V) :
    opU H t (fun v => G (s • v)) z = opU H (s • t) G (s • z) := by
  simp only [opU, smul_add, herm_smul' H s hs]

theorem opU_cmul_sum {ι : Type} (H : Sesq V) (x : V) (c : ℂ) (S : Finset ι) (d : ι → ℂ) (G : ι → V → ℂ) (z : V) :
    opU H x (fun v => c * ∑ b ∈ S, d b * G b v) z = c * ∑ b ∈ S, d b * opU H x (G b) z := by
  simp only [opU, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

end General

section Arith

theorem conj_omega (d : ℕ) : conj (omegaK d) = 1 - omegaK d := by
  rw [Formalism.L2.Th1.GD.GramFrameCompositionTwoFacts.conj_omegaK]
  unfold omegaK
  ring

theorem sqrt_sq (d : ℕ) : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

theorem trace_eq (d : ℕ) (m k : ℤ) :
    ((m : ℂ) + k * omegaK d) + conj ((m : ℂ) + k * omegaK d) = ((2 * m + k : ℤ) : ℂ) := by
  rw [map_add, map_mul, map_intCast, map_intCast, conj_omega]
  push_cast
  ring

theorem diff_sq (d : ℕ) (m k : ℤ) :
    (((m : ℂ) + k * omegaK d) - conj ((m : ℂ) + k * omegaK d)) ^ 2 = -((d * k ^ 2 : ℤ) : ℂ) := by
  rw [map_add, map_mul, map_intCast, map_intCast, conj_omega]
  have hs := sqrt_sq d
  unfold omegaK
  push_cast
  linear_combination (-(k : ℂ) ^ 2) * hs + ((k : ℂ) ^ 2 * ((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq

theorem isQInt_conj {d : ℕ} {x : ℂ} (h : IsQInt d x) : IsQInt d (conj x) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨m + k, -k, ?_⟩
  rw [map_add, map_mul, map_intCast, map_intCast, conj_omega]
  push_cast
  ring

theorem isQInt_natMul {d : ℕ} {x : ℂ} (N : ℕ) (h : IsQInt d x) : IsQInt d ((N : ℂ) * x) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨N * m, N * k, ?_⟩
  push_cast
  ring

theorem not_dvd_trace {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d) (m k : ℤ)
    (hππ : ((m : ℂ) + k * omegaK d) * conj ((m : ℂ) + k * omegaK d) = p) : ¬ (p : ℤ) ∣ 2 * m + k := by
  have hC : (((2 * m + k : ℤ) : ℂ)) ^ 2 - 4 * (p : ℂ) = -((d * k ^ 2 : ℤ) : ℂ) := by
    rw [← trace_eq d m k, ← hππ, ← diff_sq d m k]
    ring
  have hZ : (2 * m + k) ^ 2 - 4 * (p : ℤ) = -(d * k ^ 2) := by exact_mod_cast hC
  intro hdvd
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : (p : ℤ) ∣ d * k ^ 2 := by
    have e : (d * k ^ 2 : ℤ) = 4 * p - (2 * m + k) ^ 2 := by linarith
    rw [e]
    exact dvd_sub (dvd_mul_left _ _) (dvd_pow hdvd two_ne_zero)
  rcases hP.dvd_or_dvd h1 with hd | hk
  · exact hpd (Int.natCast_dvd_natCast.mp hd)
  · obtain ⟨a, ha⟩ := hdvd
    obtain ⟨b, hb⟩ := hP.dvd_of_dvd_pow hk
    rw [ha, hb] at hZ
    have e2 : (p : ℤ) * ((p : ℤ) * (a ^ 2 + d * b ^ 2)) = (p : ℤ) * 4 := by linear_combination hZ
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have e3 := mul_left_cancel₀ hp0 e2
    have h4 : (p : ℤ) ∣ 4 := ⟨_, e3.symm⟩
    have h4' : p ∣ 2 ^ 2 := by exact_mod_cast h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4'))

theorem conj_ne {d p : ℕ} (hd : 0 < d) (hp : p.Prime) (π : ℂ) (hπ : IsQInt d π) (hππ : π * conj π = p) :
    conj π ≠ π := by
  intro heq
  obtain ⟨m, k, hmk⟩ := hπ
  have h1 := diff_sq d m k
  rw [← hmk, heq, sub_self] at h1
  have h3 : (d : ℤ) * k ^ 2 = 0 := by
    have h2 : ((d * k ^ 2 : ℤ) : ℂ) = 0 := by linear_combination h1
    exact_mod_cast h2
  have hk : k = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · omega
    · exact pow_eq_zero_iff two_ne_zero |>.1 h
  subst hk
  rw [hmk] at hππ
  have h5 : ((m * m : ℤ) : ℂ) = ((p : ℤ) : ℂ) := by
    simp only [Int.cast_zero, zero_mul, add_zero, map_intCast] at hππ
    push_cast
    exact hππ
  have h6 : m * m = (p : ℤ) := by exact_mod_cast h5
  have h7 : m.natAbs * m.natAbs = p := by
    have := congrArg Int.natAbs h6
    rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
  rw [← h7] at hp
  rcases Nat.prime_mul_iff.1 hp with ⟨h8, h9⟩ | ⟨h8, h9⟩
  · rw [h9] at h8; exact Nat.not_prime_one h8
  · rw [h9] at h8; exact Nat.not_prime_one h8

theorem bezout {n : Type} (Λ : AddSubgroup (n → ℂ)) {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d) (π : ℂ)
    (hπ : IsQInt d π) (hππ : π * conj π = p) (hcΛ : ∀ x ∈ Λ, conj π • x ∈ Λ) :
    ∃ u w : ℂ, (∀ x ∈ Λ, u • x ∈ Λ) ∧ (∀ x ∈ Λ, w • x ∈ Λ) ∧ u * π + w * conj π = 1 := by
  obtain ⟨m, k, hmk⟩ := hπ
  have hT := not_dvd_trace hp hp2 hpd m k (hmk ▸ hππ)
  have hcop : IsCoprime (p : ℤ) (2 * m + k) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).2 hT
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨(b : ℂ) + (a : ℂ) * conj π, (b : ℂ), ?_, ?_, ?_⟩
  · intro x hx
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact Λ.add_mem (Λ.zsmul_mem hx b) (Λ.zsmul_mem (hcΛ x hx) a)
  · intro x hx
    rw [Int.cast_smul_eq_zsmul]
    exact Λ.zsmul_mem hx b
  · have htr := trace_eq d m k
    rw [← hmk] at htr
    have h1 : ((a * p + b * (2 * m + k) : ℤ) : ℂ) = 1 := by exact_mod_cast hab
    push_cast at h1 htr
    linear_combination (b : ℂ) * htr + (a : ℂ) * hππ + h1

end Arith

section Norms

variable {p : ℕ} [Fact p.Prime]

theorem norm_omega_le (ι : ℂ ≃+* ℂ_[p]) {d : ℕ} (hd : d % 8 = 7) : ‖ι (omegaK d)‖ ≤ 1 := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have hs := sqrt_sq d
  have hdC : (d : ℂ) + 1 = 4 * e := by exact_mod_cast he
  have hq : omegaK d ^ 2 = omegaK d - e := by
    unfold omegaK
    linear_combination (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - (1 / 4 : ℂ) * hs
      - (1 / 4 : ℂ) * hdC
  have hx : (ι (omegaK d)) ^ 2 = ι (omegaK d) - (e : ℂ_[p]) := by
    rw [← map_pow, hq, map_sub, map_natCast]
  by_contra hlt
  push Not at hlt
  have h1 : ‖ι (omegaK d)‖ ^ 2 = ‖ι (omegaK d) - (e : ℂ_[p])‖ := by rw [← norm_pow, hx]
  have h2 : ‖ι (omegaK d) - (e : ℂ_[p])‖ ≤ max ‖ι (omegaK d)‖ ‖-(e : ℂ_[p])‖ := by
    rw [sub_eq_add_neg]; exact IsUltrametricDist.norm_add_le_max _ _
  have h3 : ‖-(e : ℂ_[p])‖ ≤ 1 := by rw [norm_neg]; exact IsUltrametricDist.norm_natCast_le_one _ e
  have h4 : max ‖ι (omegaK d)‖ ‖-(e : ℂ_[p])‖ = ‖ι (omegaK d)‖ := max_eq_left (h3.trans hlt.le)
  rw [h4] at h2
  nlinarith

theorem norm_qint_le (ι : ℂ ≃+* ℂ_[p]) {d : ℕ} (hd : d % 8 = 7) {x : ℂ} (hx : IsQInt d x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨m, k, rfl⟩ := hx
  rw [map_add, map_mul, map_intCast, map_intCast]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (IsUltrametricDist.norm_intCast_le_one _ m) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ k) (norm_nonneg _) (norm_omega_le ι hd)

theorem norm_root (ι : ℂ ≃+* ℂ_[p]) (x : ℂ) (m : ℕ) (hm : 0 < m) (hx : x ^ m = 1) : ‖ι x‖ = 1 := by
  have h1 : ‖ι x‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h1

theorem norm_phase (ι : ℂ ≃+* ℂ_[p]) (y : ℝ) (N : ℕ) (hN : 0 < N) (k : ℤ) (hy : (N : ℝ) * y = k) :
    ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (y : ℂ)))‖ = 1 := by
  apply norm_root ι _ (2 * N) (by omega)
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-k, ?_⟩
  have e : (N : ℂ) * (y : ℂ) = (k : ℂ) := by exact_mod_cast hy
  push_cast
  linear_combination (-(2 * (Real.pi : ℂ) * Complex.I)) * e

theorem norm_sign (ι : ℂ ≃+* ℂ_[p]) (x : ℂ) (hx : x = 1 ∨ x = -1) : ‖ι x‖ = 1 := by
  rcases hx with rfl | rfl <;> simp

theorem norm_p_lt : ‖(p : ℂ_[p])‖ < 1 := by
  have h1 := PadicComplex.norm_extends' p (p : ℚ_[p])
  rw [Padic.norm_p] at h1
  have h2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by simpa using h1
  rw [h2]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem dvd_of_norm_lt (T : ℤ) (h : ‖(T : ℂ_[p])‖ < 1) : (p : ℤ) ∣ T := by
  by_contra hT
  obtain ⟨a, b, hab⟩ :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).irreducible).2 hT
  have h1 : ((a : ℂ_[p]) * (p : ℂ_[p]) + (b : ℂ_[p]) * (T : ℂ_[p])) = 1 := by exact_mod_cast hab
  have h2 := IsUltrametricDist.norm_add_le_max ((a : ℂ_[p]) * (p : ℂ_[p])) ((b : ℂ_[p]) * (T : ℂ_[p]))
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have h3 : ‖(a : ℂ_[p])‖ * ‖(p : ℂ_[p])‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ a)) norm_p_lt
  have h4 : ‖(b : ℂ_[p])‖ * ‖(T : ℂ_[p])‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ b)) h
  exact absurd h2 (not_le.2 (max_lt h3 h4))

end Norms

theorem linSubst_eq {K : Type} [Field K] {m n : Type} [Fintype n] (M : Matrix m n K) (T : MvPowerSeries m K) :
    linSubst M T = linSub (fun i j => M i j) T := rfl

theorem linSub_sumC {K : Type} [Field K] {n m ι : Type} [Finite n] [Fintype m] [Fintype ι] (Fm : n → m → K)
    (cc : ι → K) (T : ι → MvPowerSeries n K) :
    linSub Fm (∑ i, MvPowerSeries.C (cc i) * T i) = ∑ i, MvPowerSeries.C (cc i) * linSub Fm (T i) := by
  rw [← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C]

end XiConnection

theorem XiConnection.pow_aux (u w : ℂ) (hw : w ≠ 0) (hu : u ≠ 0) :
    (u / w) ^ 4 * ((w * u) ^ 4)⁻¹ * (w * u) ^ 8 = u ^ 8 := by
  field_simp

theorem XiConnection.atMostLine_of (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hSD : IsSelfDual (matH h) Λ) (hSt : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ)
    (θ : (n → ℂ) → ℂ) (hθ : θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ) (hθ0 : θ ≠ 0)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hLN : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι) :
    Formalism.L2.Th1.H.AtMostLine (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ := by
  obtain ⟨g₁, ε, hI, hidx, hidx2, hε, htens⟩ := hLN
  have hidx1 : relIdx (Formalism.L2.Th1.H.stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (Formalism.L2.Th1.H.pow4 Λ)) ≠ 0 := by
    intro h0; exact hidx (h0 ▸ dvd_zero p)
  have hS := Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ dK ha hdK lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g₁ hI hSD hSt
    hidx1 hidx2
  have hε0 : ε ≠ 0 := by
    rintro rfl
    obtain ⟨z0, hz0⟩ : ∃ z0, θ z0 ≠ 0 := by
      by_contra hc; push Not at hc; exact hθ0 (funext hc)
    have h4 := congrFun htens (fun x => z0 x.2)
    simp only [Formalism.L2.Th1.H.tens4, zero_smul, Pi.zero_apply] at h4
    rw [Finset.prod_eq_zero_iff] at h4
    obtain ⟨_, _, h5⟩ := h4
    exact hz0 h5
  obtain ⟨-, hall⟩ := Formalism.L2.Th1.H.thetaVector _ _ n h Λ _ _ g₁ hS ε hε0
  obtain ⟨-, -, hspan⟩ := hall θ hθ htens
  intro θ' hθ' hθ'0 F hF
  obtain ⟨c1, hc1⟩ := hspan F hF
  obtain ⟨c2, hc2⟩ := hspan θ' hθ'
  have hc2' : c2 ≠ 0 := by rintro rfl; rw [zero_smul] at hc2; exact hθ'0 hc2
  exact ⟨c1 / c2, by rw [hc1, hc2, smul_smul, div_mul_cancel₀ _ hc2']⟩

theorem XiConnection.ser_eq {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (θ : (n → ℂ) → ℂ) (hθ : AnalyticOnNhd ℂ θ Set.univ) {κx κ' : Type} [Fintype κx] [Fintype κ']
    (F : (n → ℂ) → ℂ) (r : κx → ℂ) (t : κx → n → ℂ) (co : κ' → ℂ) (pt : κ' → n → ℂ) (s : ℂ)
    (hfun : (fun z => ∑ k, r k * opU (matH h) (t k) F z) = fun z => ∑ kb, co kb * opU (matH h) (pt kb) θ (s • z))
    {J ν : Type} [Fintype J] [Fintype ν] (v : J → n → ℂ) (A : J → ν → ℂ_[p]) :
    serLin ι h F r t (frameM (ι : ℂ →+* ℂ_[p]) v A) =
      thetaLin (ι : ℂ →+* ℂ_[p]) h θ (fun kb => ι (co kb)) pt
        (frameM (ι : ℂ →+* ℂ_[p]) v (fun j x => ι s * A j x)) := by
  have hFan : ∀ kb, AnalyticAt ℂ (opU (matH h) (pt kb) θ) 0 := fun kb =>
    Formalism.L2.Th1.H.opUAnalytic (n → ℂ) (matH h) (pt kb) θ hθ 0 (Set.mem_univ _)
  obtain ⟨hGan, hGtay⟩ := Formalism.L2.Th1.H.FormalGroupLawNegation.taylorMv_sum Formalism.L2.Th1.H.taylorMvLinear
    (Finset.univ : Finset κ') co (fun kb => opU (matH h) (pt kb) θ) hFan
  have hcomp : taylorMv (fun w => ∑ kb ∈ (Finset.univ : Finset κ'),
      co kb * opU (matH h) (pt kb) θ ((Matrix.diagonal fun _ => s).mulVec w)) =
      linSubst (Matrix.diagonal fun _ => s)
        (taylorMv fun z => ∑ kb ∈ (Finset.univ : Finset κ'), co kb * opU (matH h) (pt kb) θ z) :=
    Formalism.L2.Th1.H.taylorMvComp n n (Matrix.diagonal fun _ => s)
      (fun z => ∑ kb ∈ (Finset.univ : Finset κ'), co kb * opU (matH h) (pt kb) θ z) hGan
  have hmv : ∀ w : n → ℂ, (Matrix.diagonal fun _ => s).mulVec w = s • w := fun w => by
    funext i; rw [Matrix.mulVec_diagonal]; rfl
  have hfun2 : (fun z => ∑ kb ∈ (Finset.univ : Finset κ'), co kb * opU (matH h) (pt kb) θ (s • z)) =
      fun w => ∑ kb ∈ (Finset.univ : Finset κ'),
        co kb * opU (matH h) (pt kb) θ ((Matrix.diagonal fun _ => s).mulVec w) := by
    funext w; rw [hmv]
  have hmat : (fun i x => ∑ w, (fun i j => ((Matrix.diagonal fun _ => s).map (ι : ℂ →+* ℂ_[p])) i j) i w *
      frameM (ι : ℂ →+* ℂ_[p]) v A w x) = frameM (ι : ℂ →+* ℂ_[p]) v (fun j x => ι s * A j x) := by
    funext i x
    simp only [Matrix.map_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, RingEquiv.coe_toRingHom]
      unfold frameM
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro w _ hw
      rw [if_neg (Ne.symm hw), map_zero, zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  unfold serLin
  rw [hfun, hfun2, hcomp, Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst, linSubst_eq, Formalism.L2.Th1.GD.GramFrameCompositionLinFacts.linSub_linSub,
    hmat, hGtay, map_sum]
  simp only [map_mul, MvPowerSeries.map_C]
  rw [linSub_sumC]
  rfl

open XiConnection in
theorem xiConn_of (h1 : EtLoc) (h2 : ScalarConst) (h3 : XiSwap) : XiConn := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ h Λ hHerm hPos hLat hSD hSt θ hθ p _ hp2 hpd ι hIC hLN π hπ hππ hπ1
    Sa Sb hSa hSb Ψ hΨ κx _ r t N hr hN hpN hNt J _ v hv ν _ A hA
  by_cases hθ0 : θ = 0
  · subst hθ0
    have e : (fun z => ∑ k, r k * opU (matH h) (t k)
        (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) 0 (p ^ Fintype.card n) Ψ Sa Sb) z) =
        fun _ => (0 : ℂ) := by
      funext z
      simp [xiG, opU]
    have e0 : taylorMv (fun _ : n → ℂ => (0 : ℂ)) = 0 := by
      have := (Formalism.L2.Th1.H.taylorMvLinear n (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) analyticAt_const
        analyticAt_const).2 0
      simpa using this
    unfold serLin
    rw [e, e0, map_zero, ← Formalism.L2.Th1.G.linSubHom_apply, map_zero]
    intro κ
    simp
  have hp : p.Prime := Fact.out
  have hb := TensorIntegralTorsion.odd_b hcm
  have hQ : ∀ a : ℂ, IsQInt dK a → ∀ x ∈ Λ, a • x ∈ Λ := fun a ha x hx =>
    TensorIntegralTorsion.qint_smul_mem Λ b₀ dK hb hSt a ha x hx
  have hπΛ := hQ π hπ
  have hπcΛ := hQ (conj π) (isQInt_conj hπ)
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hππ; exact hp.ne_zero (by exact_mod_cast hππ.symm)
  have hπc0 : conj π ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hππ; exact hp.ne_zero (by exact_mod_cast hππ.symm)
  have hne := conj_ne hdK hp π hπ hππ
  have hbez := bezout Λ hp hp2 hpd π hπ hππ hπcΛ
  have hsemi : Formalism.L2.Th1.H.IsSemiChar (matH h) Λ (alphaQ (Real.sqrt dK / 2) (matH h)) :=
    (Formalism.L2.Th1.H.alphaQSemi (n → ℂ) (matH h) hHerm b₀ dK hb Λ (le_of_eq hSD.symm) hSt).2.2
  have hline := atMostLine_of a₀ b₀ c₀ dK ha hdK lam hlam hcm n h Λ hSD hSt θ hθ hθ0 p ι hLN
  obtain ⟨hcard, c, hc8, hscal⟩ := h2 dK n h Λ hHerm hPos hLat hSD hsemi hline p hp π hππ hne hπΛ hπcΛ hbez
    Sa hSa θ hθ hθ0
  have hsq0 : ((Real.sqrt ((p : ℝ) ^ Fintype.card n) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt ((p : ℝ) ^ Fintype.card n) :=
      Real.sqrt_pos.2 (pow_pos (by exact_mod_cast hp.pos) _)
    exact_mod_cast this.ne'
  have hsq2 : ((Real.sqrt ((p : ℝ) ^ Fintype.card n) : ℝ) : ℂ) ^ 2 = (p : ℂ) ^ Fintype.card n := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hc8
    exact (pow_ne_zero _ (div_ne_zero hπc0 hπ0)) hc8.symm
  have hswap := h3 dK n h Λ hHerm hSD hsemi (p ^ Fintype.card n) (pow_pos hp.pos _) π hπ0 hπΛ hπcΛ Sa Sb hSa hSb
    θ hθ _ (mul_ne_zero hc0 (inv_ne_zero hsq0)) hscal Ψ
  set D : ℂ := c * ((Real.sqrt ((p : ℝ) ^ Fintype.card n) : ℝ) : ℂ)⁻¹ * ((p ^ Fintype.card n : ℕ) : ℂ) with hD_def
  have hD8 : D ^ 8 = (conj π) ^ (8 * Fintype.card n) := by
    have e1 : D ^ 8 = c ^ 8 * (((((Real.sqrt ((p : ℝ) ^ Fintype.card n) : ℝ) : ℂ)) ^ 2) ^ 4)⁻¹ *
        ((p : ℂ) ^ Fintype.card n) ^ 8 := by
      rw [hD_def]; push_cast; ring
    rw [e1, hc8, hsq2, ← hππ]
    rw [pow_mul', pow_mul', div_pow, mul_pow]
    exact pow_aux _ _ (pow_ne_zero _ hπ0) (pow_ne_zero _ hπc0)
  have hDn : ‖ι D‖ = 1 := by
    have h8 : ‖ι D‖ ^ 8 = 1 := by rw [← norm_pow, ← map_pow, hD8, map_pow, norm_pow, hπ1, one_pow]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h8
  set s : ℂ := π / conj π with hs_def
  have hs : s * conj s = 1 := by rw [hs_def, map_div₀, Complex.conj_conj]; field_simp

  have hSbΛ : ∀ b ∈ Sb, b ∈ Λ := hSb.1
  obtain ⟨pt, hpt⟩ : ∃ pt : κx × Sb → n → ℂ, ∀ kb, pt kb = s • (t kb.1 + (kb.2 : n → ℂ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨co, hco⟩ : ∃ co : κx × Sb → ℂ, ∀ kb, co kb = r kb.1 * D⁻¹ * Ψ kb.2 *
      alphaQ (Real.sqrt dK / 2) (matH h) kb.2 *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (s • t kb.1) (s • (kb.2 : n → ℂ)) : ℂ)) :=
    ⟨_, fun _ => rfl⟩
  have hfun : (fun z => ∑ k, r k * opU (matH h) (t k)
      (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) z) =
      fun z => ∑ kb ∈ (Finset.univ : Finset (κx × Sb)), co kb * opU (matH h) (pt kb) θ (s • z) := by
    funext z
    have hk : ∀ k, opU (matH h) (t k)
        (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) z =
        D⁻¹ * ∑ b ∈ Sb, (Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b) *
          (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (s • t k) (s • b) : ℂ)) *
            opU (matH h) (s • t k + s • b) θ (s • z)) := by
      intro k
      have e1 := opU_smul_iso (matH h) s hs
        (fun w => D⁻¹ * ∑ b ∈ Sb, (Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b) * opU (matH h) (s • b) θ w) (t k) z
      have e2 := opU_cmul_sum (matH h) (s • t k) D⁻¹ Sb (fun b => Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b)
        (fun b => opU (matH h) (s • b) θ) (s • z)
      rw [show xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb =
          fun v => D⁻¹ * ∑ b ∈ Sb, (Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b) *
            opU (matH h) (s • b) θ (s • v) from funext hswap]
      refine e1.trans (e2.trans ?_)
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Formalism.L2.Th1.H.opUMul (n → ℂ) (matH h) hHerm (s • t k) (s • b) θ (s • z)]
    simp only [hk]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hco, hpt]
    rw [← Finset.sum_coe_sort Sb, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_add]
    ring
  have hser := ser_eq ι h θ hθ.1 _ r t co pt s hfun v A
  have hNp : ‖((N * p : ℕ) : ℂ_[p])‖ = ‖(p : ℂ_[p])‖ := by
    push_cast; rw [norm_mul, LocalJetRescaling.norm_natCast p hpN, one_mul]
  have hπn : ‖ι π‖ = ‖(p : ℂ_[p])‖ := by
    have e := congrArg (fun x => ‖ι x‖) hππ
    simp only [map_mul, norm_mul, map_natCast, hπ1, mul_one] at e
    exact e
  have hsn : ‖ι s‖ = ‖(p : ℂ_[p])‖ := by rw [hs_def, map_div₀, norm_div, hπ1, div_one, hπn]
  have hNb : ∀ kb : κx × Sb, (N : ℂ) • t kb.1 + (N : ℂ) • (kb.2 : n → ℂ) ∈ Λ := fun kb =>
    Λ.add_mem (hNt kb.1) (by rw [Nat.cast_smul_eq_nsmul]; exact Λ.nsmul_mem (hSbΛ _ kb.2.2) N)
  have hαt : ∀ kb, ((N : ℂ) * conj π) • pt kb ∈ Λ := by
    intro kb
    have e : (N : ℂ) * conj π * s = π * N := by rw [hs_def]; field_simp
    rw [hpt, smul_smul, e, mul_smul, smul_add]
    exact hπΛ _ (hNb kb)
  have hMt : ∀ kb, ((N * p : ℕ) : ℂ) • pt kb ∈ Λ := by
    intro kb
    have e : ((N * p : ℕ) : ℂ) * s = π * (π * N) := by
      rw [hs_def]; push_cast; rw [← hππ]; field_simp
    rw [hpt, smul_smul, e, mul_smul, mul_smul, smul_add]
    exact hπΛ _ (hπΛ _ (hNb kb))
  have hr' : ∀ kb, ‖ι (co kb)‖ ≤ 1 := by
    intro kb
    have hα1 : ‖ι (alphaQ (Real.sqrt dK / 2) (matH h) kb.2)‖ = 1 :=
      norm_sign ι _ (hsemi.1 _ (hSbΛ _ kb.2.2))
    obtain ⟨m, hm⟩ : ∃ m : ℤ, altE (matH h) ((N : ℂ) • t kb.1) (kb.2 : n → ℂ) = m := by
      have hx : (N : ℂ) • t kb.1 ∈ dualLat (matH h) Λ := by rw [hSD]; exact hNt kb.1
      exact hx _ (hSbΛ _ kb.2.2)
    have hy : (N : ℝ) * altE (matH h) (s • t kb.1) (s • (kb.2 : n → ℂ)) = m := by
      rw [← hm]
      unfold altE
      rw [herm_smul' (matH h) s hs]
      simp
    have hζ1 := norm_phase ι _ N hN m hy
    have e : ‖ι (co kb)‖ = ‖ι (r kb.1)‖ * ‖ι (Ψ kb.2)‖ := by
      rw [hco]
      simp only [map_mul, norm_mul, map_inv₀, norm_inv, hDn, hα1, hζ1, inv_one, mul_one]
    rw [e]
    exact mul_le_one₀ (hr _) (norm_nonneg _) (hΨ _ kb.2.2)
  have hunit : ‖ι ((N : ℂ) * conj π)‖ = 1 := by
    rw [map_mul, norm_mul, map_natCast, LocalJetRescaling.norm_natCast p hpN, hπ1, one_mul]
  have hA' : ∀ j x, ‖ι s * A j x‖ ≤ ‖((N * p : ℕ) : ℂ_[p])‖ := fun j x => by
    rw [norm_mul, hsn, hNp]; exact mul_le_of_le_one_right (norm_nonneg _) (hA j x)
  have hE := h1 a₀ b₀ c₀ dK ha hdK lam hlam hcm n h Λ hSD hSt θ hθ p hp2 hpd ι hIC hLN (κx × Sb)
    (fun kb => ι (co kb)) pt ((N : ℂ) * conj π) (N * p) hr' (isQInt_natMul N (isQInt_conj hπ)) hunit
    (Nat.mul_pos hN hp.pos) hαt hMt J v hv ν (fun j x => ι s * A j x) hA'
  rw [hser]
  exact hE.1

open XiConnection in
theorem split_bound_of_xi_lemmas (h1 : XiEt) (h2 : XiConn) : SelfDualLatticeThetaPadicIntegrality := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm n _ _ h Λ hHerm hPos hLat hSD hSt θ hθ p _ hp2 hpd ι hIC hLN π hπ hππ
    Sa Sb hSa hSb Ψ hΨ κx _ r t N hr hN hpN hNt J _ v hv ν _ A hA
  have hp : p.Prime := Fact.out
  have hd7 : dK % 8 = 7 := hcm.2.2.1
  have hle : ‖ι (conj π)‖ ≤ 1 := norm_qint_le ι hd7 (isQInt_conj hπ)
  have hprod : ‖ι π‖ * ‖ι (conj π)‖ = ‖(p : ℂ_[p])‖ := by
    rw [← norm_mul, ← map_mul, hππ, map_natCast]
  rcases hle.lt_or_eq with hlt | heq
  · have hπle : ‖ι π‖ ≤ 1 := norm_qint_le ι hd7 hπ
    have hπ1 : ‖ι π‖ = 1 := by
      rcases hπle.lt_or_eq with hlt' | h'
      · exfalso
        obtain ⟨m, k, hmk⟩ := hπ
        have hT := not_dvd_trace hp hp2 hpd m k (hmk ▸ hππ)
        have htr := trace_eq dK m k
        rw [← hmk] at htr
        have h3 : ‖((2 * m + k : ℤ) : ℂ_[p])‖ < 1 := by
          rw [← map_intCast ι, ← htr, map_add]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlt' hlt)
        exact hT (dvd_of_norm_lt _ h3)
      · exact h'
    have hpb : ‖ι (conj π)‖ = ‖(p : ℂ_[p])‖ := by rw [← hprod, hπ1, one_mul]
    exact h1 a₀ b₀ c₀ dK ha hdK lam hlam hcm n h Λ hHerm hPos hLat hSD hSt θ hθ p hp2 hpd ι hIC hLN π hπ hππ hlt
      Sa Sb hSa hSb Ψ hΨ κx r t N hr hN hpN hNt J v hv ν A (fun j x => (hA j x).trans hpb.le)
  · have hJ := h2 a₀ b₀ c₀ dK ha hdK lam hlam hcm n h Λ hHerm hPos hLat hSD hSt θ hθ p hp2 hpd ι hIC hLN π hπ hππ heq
      Sa Sb hSa hSb Ψ hΨ κx r t N hr hN hpN hNt J v hv ν A (fun j x => (hA j x).trans heq.le)
    intro κ
    rw [MvPowerSeries.coeff_C_mul, mul_left_comm, norm_mul]
    have hpn : ‖(p : ℂ_[p]) ^ Fintype.card n‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ p)
    calc _ ≤ 1 * 1 := mul_le_mul hpn (hJ κ) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

end Formalism.L2.AlgTh
