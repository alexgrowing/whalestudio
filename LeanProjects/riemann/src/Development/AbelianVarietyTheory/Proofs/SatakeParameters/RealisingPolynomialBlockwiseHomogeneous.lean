import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjectiveStatement

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.BlockHom

open MvPolynomial

theorem two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow, Complex.norm_ofNat] at h'
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h'

theorem eval_aeval_gen {σ κ : Type} (g : κ → ℂ) (φ : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    MvPolynomial.eval g (MvPolynomial.aeval φ Q) = MvPolynomial.eval (fun s => MvPolynomial.eval g (φ s)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, aeval_X, map_mul, hp, eval_X]

open Classical in
theorem evFr_scale (D : D7) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (τ₀ : D.what₂.Tau) (t : ℂ) (ht : t ≠ 0) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q y := by
  set β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => if τ = τ₀ then t • (1 : Matrix (Fin n) (Fin n) ℂ) else 1 with hβ
  have hB : IsBor β := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [hβ]; split_ifs <;> simp [Matrix.one_apply_ne (ne_of_lt hsr).symm]
    · simp only [hβ]; split_ifs <;> simp [ht]
  have h1 := congrArg (MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2)) (hQ β hB)
  have hL : MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2) (colSub β Q) =
      GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) := by
    unfold colSub GL3Theta.evFr
    rw [eval_aeval_gen]
    apply congrArg (fun F => MvPolynomial.eval F Q)
    funext k
    simp only [map_sum, map_mul, eval_C, eval_X, hβ]
    by_cases hk : k.1 = τ₀
    · simp [hk, Matrix.one_apply, mul_comm]
    · simp [hk, Matrix.one_apply]
  rw [← hL, h1, MvPolynomial.smul_eval]
  unfold GL3Theta.evFr
  congr 1
  rw [Finset.prod_eq_single τ₀]
  · simp [hβ, Finset.prod_pow_eq_pow_sum]
  · intro τ _ hτ
    simp [hβ, hτ]
  · simp

open Classical in
theorem prod_scale {ι : Type} [Fintype ι] (τ₀ : ι) (A B : ι → ℂ) (k : ℂ)
    (hAB : ∀ τ, A τ = if τ = τ₀ then k * B τ else B τ) (e : ι → ℤ) :
    ∏ τ, A τ ^ e τ = k ^ e τ₀ * ∏ τ, B τ ^ e τ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), ← Finset.mul_prod_erase (s := Finset.univ) (fun τ => B τ ^ e τ) (Finset.mem_univ τ₀)]
  rw [hAB τ₀, if_pos rfl, mul_zpow, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro τ hτ
  rw [hAB τ, if_neg (Finset.ne_of_mem_erase hτ)]

open Classical in
theorem zT_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det) (τ₀ : D.what₂.Tau) (c : ℂ) (hc : c ≠ 0)
    (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then c⁻¹ else c) • f τ else f τ) (τ : D.what₂.Tau) :
    zT X D pos f' τ = if τ = τ₀ then c • zT X D pos f τ else zT X D pos f τ := by
  unfold zT
  rw [hf' τ]
  by_cases hτ : τ = τ₀
  · subst hτ
    simp only [if_true]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [ho, if_true]
      rw [show c⁻¹ • f τ = (Units.mk0 c⁻¹ (inv_ne_zero hc)) • f τ from rfl, Matrix.inv_smul' (k := Units.mk0 c⁻¹ (inv_ne_zero hc)) (h := hf τ)]
      ext a b
      simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def]
    · simp [ho]
  · simp [hτ]

def dg {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) (τ₀ : D.what₂.Tau)
    (m : Var (X.Pj i) →₀ ℕ) : ℕ :=
  ∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then m x else 0

open Classical in
theorem valZ_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det)
    (τ₀ : D.what₂.Tau) (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f τ else f τ) :
    valZ X D pos i h R f' = valZ X D pos i h (∑ m ∈ R.support, monomial m (coeff m R * 2 ^ (dg X D pos i τ₀ m))) f := by
  have hg : ∀ x : Var (X.Pj i), zT X D pos f' (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) =
      (2:ℂ) ^ (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) *
        zT X D pos f (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) := by
    intro x
    rw [zT_scale X D pos f f' hf τ₀ 2 two_ne_zero hf']
    by_cases hb : (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀
    · have e : posJ X D pos i ⟨x.1, x.2.1⟩ = τ₀ := by rw [hb]; simp
      simp [e, hb]
    · have e : posJ X D pos i ⟨x.1, x.2.1⟩ ≠ τ₀ := fun e => hb (by rw [← e]; simp)
      simp [e, hb]
  unfold valZ
  rw [MvPolynomial.eval_eq, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hsum : (∑ x ∈ m.support, (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) * m x) = dg X D pos i τ₀ m := by
    unfold dg
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
    · intro x _ hx
      have hx0 : m x = 0 := by simpa using hx
      simp [hx0]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
  simp only [hg, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [hsum, Finset.prod_subset (Finset.subset_univ m.support) (fun x _ hx => by
    have hx0 : m x = 0 := by simpa using hx
    simp [hx0])]
  ring

theorem realises_blockHom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  intro p _ X D pos i n h a ν Q R hQ hR m hm τ₀
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = if IsOddPos (pos.symm τ₀).2 then -1 else 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2 := ⟨_, rfl⟩
  have htε : t = (2:ℂ) ^ ε := by
    rw [ht, hε]; split_ifs <;> simp
  have ht0 : t ≠ 0 := by rw [htε]; exact zpow_ne_zero _ two_ne_zero
  obtain ⟨R2, hR2⟩ : ∃ R2 : XR (X.Pj i) ℂ, R2 = ∑ m ∈ R.support, monomial m (coeff m R * 2 ^ (dg X D pos i τ₀ m)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * ((t ^ n) ^ (-(a τ₀)) * t ^ (∑ r, ν τ₀ r)) := ⟨_, rfl⟩
  have key : ∀ f : Fr1 D n, ev1 X D pos i h R2 f = c * ev1 X D pos i h R f := by
    intro f
    have hfu : ∀ τ, IsUnit (f.1 τ).det := f.2
    let f' : Fr1 D n := ⟨fun τ => if τ = τ₀ then t • f.1 τ else f.1 τ, by
      intro τ
      by_cases hτ : τ = τ₀
      · simp only [hτ, if_true, Matrix.det_smul]
        exact (IsUnit.mk0 _ (pow_ne_zero _ ht0)).mul (hfu τ₀)
      · simp only [hτ, if_false]; exact hfu τ⟩
    have hf' : ∀ τ, f'.1 τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f.1 τ else f.1 τ := by
      intro τ; rw [← ht]
    have e1 := GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue X D pos i h R2 f
    have e2 := GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue X D pos i h R f'
    have e3 := hR f'
    have e4 := hR f
    have hv : valZ X D pos i h R f'.1 = valZ X D pos i h R2 f.1 := by
      rw [hR2]; exact valZ_scale X D pos i h R f.1 f'.1 hfu τ₀ hf'
    have hdz : ∏ τ, (zT X D pos f'.1 τ).det ^ eT X D pos i τ =
        ((2:ℂ) ^ n) ^ eT X D pos i τ₀ * ∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ := by
      apply prod_scale
      intro τ
      rw [zT_scale X D pos f.1 f'.1 hfu τ₀ 2 two_ne_zero hf' τ]
      split_ifs <;> simp [Matrix.det_smul]
    have hdf : ∏ τ, (f'.1 τ).det ^ (-(a τ)) = (t ^ n) ^ (-(a τ₀)) * ∏ τ, (f.1 τ).det ^ (-(a τ)) := by
      apply prod_scale
      intro τ
      show (if τ = τ₀ then t • f.1 τ else f.1 τ).det = _
      split_ifs <;> simp [Matrix.det_smul]
    have hq : GL3Theta.evFr D Q f'.1 = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q f.1 := evFr_scale D ν Q hQ τ₀ t ht0 f.1
    have hK : ((2:ℂ) ^ n) ^ eT X D pos i τ₀ ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ two_ne_zero)
    have hE := e2.symm.trans e3
    rw [hv, hdz, hdf, hq] at hE
    rw [e1, e4, hc]
    calc (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1
        = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * (((2:ℂ) ^ n) ^ eT X D pos i τ₀ *
            (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1) := by
          field_simp
      _ = _ := by rw [hE]; ring
  have hz : R2 - c • R = 0 := by
    apply GlobalTheory.T.evalModelPolynomialOnStdFrames_injective X D pos i h
    intro f
    rw [map_sub, map_smul]
    simp [key f]
  have hcoef : coeff m R2 = coeff m R * 2 ^ (dg X D pos i τ₀ m) := by
    rw [hR2, coeff_sum]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hm'; exact absurd hm hm'
  have hm0 : coeff m R ≠ 0 := (mem_support_iff.mp hm)
  have h2 : (2:ℂ) ^ (dg X D pos i τ₀ m) = c := by
    have := congrArg (coeff m) hz
    rw [coeff_sub, coeff_smul, hcoef, coeff_zero, sub_eq_zero, smul_eq_mul] at this
    exact mul_left_cancel₀ hm0 (by rw [this]; ring)
  have hcz : c = (2:ℂ) ^ (-((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ))) := by
    have a1 : ((2:ℂ) ^ n) ^ (eT X D pos i τ₀) = (2:ℂ) ^ ((n : ℤ) * eT X D pos i τ₀) := by rw [zpow_mul, zpow_natCast]
    have a2 : (((2:ℂ) ^ ε) ^ n) ^ (-(a τ₀)) = (2:ℂ) ^ (ε * ((n : ℤ) * (-(a τ₀)))) := by rw [zpow_mul, zpow_mul, zpow_natCast]
    have a3 : ((2:ℂ) ^ ε) ^ (∑ r, ν τ₀ r) = (2:ℂ) ^ (ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) := by rw [zpow_mul, zpow_natCast]
    rw [hc, htε, a1, a2, a3, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_neg]
  have hfin : ((dg X D pos i τ₀ m : ℕ) : ℤ) = -((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) :=
    two_zpow_inj (by rw [zpow_natCast, h2, hcz])
  unfold dg at hfin
  push_cast at hfin
  rw [hfin, hε]
  ring

end GlobalTheory.TwV.DelA.BlockHom
