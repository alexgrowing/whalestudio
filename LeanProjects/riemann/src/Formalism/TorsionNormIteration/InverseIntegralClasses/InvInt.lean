import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

open PowerSeries

universe u v

namespace Formalism.LT.InvIntP

open Formalism.G Formalism.G.LogCR

section Basic

variable {K : Type u} [NormedField K] {ι : Type v}

def Low (m : ℕ) (x : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0

theorem Low.mono {m k : ℕ} {x : MvPowerSeries ι K} (h : Low m x) (hk : k ≤ m) : Low k x := by
  exact fun d hd => h d (lt_of_lt_of_le hd hk)

theorem Low.mul {m k : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ab hab => ?_
  have hab' : ab.1 + ab.2 = d := by simpa using hab
  have hdeg : ab.1.degree + ab.2.degree = d.degree := by rw [← hab', map_add]
  by_cases h1 : ab.1.degree < m
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]

theorem Low.add {m : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low m y) :
    Low m (x + y) := by
  intro d hd
  rw [map_add, hx d hd, hy d hd, add_zero]

theorem Low.sub {m : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low m y) :
    Low m (x - y) := by
  intro d hd
  rw [map_sub, hx d hd, hy d hd, sub_zero]

theorem low_zero (x : MvPowerSeries ι K) : Low 0 x := by
  intro d hd
  exact absurd hd (Nat.not_lt_zero _)

theorem low_one {x : MvPowerSeries ι K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have h0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx]

end Basic

section Ultra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem integral_mul {A B : MvPowerSeries ι K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ab _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) (hB _)

theorem integral_one : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_pow {A : MvPowerSeries ι K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv (A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact integral_one
  | succ n ih =>
    rw [pow_succ]
    exact integral_mul ih hA

theorem integralSubst (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    IntegralMv (f.subst P) := by
  intro e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hP0)]
  by_cases hfin : (Function.support fun n : ℕ => PowerSeries.coeff n f • MvPowerSeries.coeff e (P ^ n)).Finite
  · rw [finsum_eq_sum _ hfin]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
    rw [norm_smul]
    exact mul_le_one₀ (hf n) (norm_nonneg _) (integral_pow hP n e)
  · rw [finsum_of_infinite_support hfin, norm_zero]
    exact zero_le_one

end Ultra

theorem coeff_expand_low {K : Type u} [NormedField K] {ι : Type v} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (σ : K →+* K) (D : MvPowerSeries ι K) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) :
    MvPowerSeries.coeff d (MvPowerSeries.expand q hq (MvPowerSeries.map σ D)) = 0 := by
  classical
  by_cases hall : ∀ i, q ∣ d i
  · set m : ι →₀ ℕ := Finsupp.mapRange (fun k => k / q) (Nat.zero_div q) d with hm
    have hdm : d = q • m := by
      ext i
      simp only [Finsupp.smul_apply, smul_eq_mul, hm, Finsupp.mapRange_apply]
      exact (Nat.mul_div_cancel' (hall i)).symm
    have hdeg : d.degree = q * m.degree := by rw [hdm, map_nsmul, smul_eq_mul]
    have hmlt : m.degree < N := by
      rcases Nat.eq_zero_or_pos m.degree with h0 | hpos
      · omega
      · nlinarith
    rw [hdm, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map, hlow m hmlt, map_zero]
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    exact MvPowerSeries.coeff_expand_of_not_dvd q hq _ hi

theorem funEqLowCoeff {K : Type u} [NormedField K] {ι : Type v} (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K) (hq2 : 2 ≤ q) (D : MvPowerSeries ι K) (hD : IsFunEqTypeMv p q hq σ D)
    (N : ℕ) (hN : 1 ≤ N) (hlow : ∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) : ‖MvPowerSeries.coeff d D‖ ≤ 1 := by
  have h := hD d
  rwa [map_sub, map_smul, coeff_expand_low q hq hq2 σ D N hN hlow d hd, smul_zero, sub_zero] at h

section Inv

variable {K : Type u} [NormedField K] {ι : Type v}

def tail2 (f : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff (n + 2) f

theorem decomp (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) :
    f = X + X ^ 2 * tail2 f := by
  ext n
  rcases n with _ | _ | n <;>
    simp [tail2, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, h0, h1]

theorem subst_eq (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {a : MvPowerSeries ι K} (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = a + a ^ 2 * (tail2 f).subst a := by
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  conv_lhs => rw [decomp f h0 h1]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

theorem agree_psubst [Finite ι] (g : PowerSeries K) {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Agree N (g.subst a) (g.subst b) := by
  exact Agree.subst (f := g) (f' := g) (a := fun _ : Unit => a) (a' := fun _ : Unit => b)
    (fun _ => ha0) (fun _ => hb0) (fun _ _ => rfl) (fun _ => hab)

theorem low_of_agree {N : ℕ} {a b : MvPowerSeries ι K} (hab : Agree N a b) : Low N (a - b) := by
  intro d hd
  rw [map_sub, hab d hd, sub_self]

theorem key [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) (f.subst a - f.subst b - (a - b)) := by
  rw [subst_eq f h0 h1 ha0, subst_eq f h0 h1 hb0]
  have e : a + a ^ 2 * (tail2 f).subst a - (b + b ^ 2 * (tail2 f).subst b) - (a - b) =
      (a - b) * (a + b) * (tail2 f).subst a + b ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) := by ring
  rw [e]
  have hd : Low N (a - b) := low_of_agree hab
  have hs : Low 1 (a + b) := low_one (by simp [ha0, hb0])
  have hb2 : Low 2 (b ^ 2) := by
    have := (low_one hb0).mul (low_one hb0)
    rw [pow_two]
    exact this
  refine Low.add ?_ ?_
  · have := (hd.mul hs).mul (low_zero ((tail2 f).subst a))
    simpa using this
  · exact (hb2.mul (low_of_agree (agree_psubst _ ha0 hb0 hab))).mono (by omega)

end Inv

theorem invIntegralOfClass (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v)
    [Finite ι] (C : MvPowerSeries ι K → Prop) (f : PowerSeries K)
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : MvPowerSeries ι K, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P))
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0) (hCh : C (f.subst h)) :
    IntegralMv h := by
  have main : ∀ N : ℕ, ∀ d : ι →₀ ℕ, d.degree < N → ‖MvPowerSeries.coeff d h‖ ≤ 1 := by
    intro N
    induction N with
    | zero =>
      intro d hd
      omega
    | succ N ih =>
      intro d hd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hlt | heq
      · exact ih d hlt
      · rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · subst hN0
          have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 heq
          subst hd0
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, norm_zero]
          exact zero_le_one
        · let T : MvPowerSeries ι K := fun e => if e.degree < N then MvPowerSeries.coeff e h else 0
          have hTc : ∀ e, MvPowerSeries.coeff e T = if e.degree < N then MvPowerSeries.coeff e h else 0 :=
            fun e => rfl
          have hT0 : MvPowerSeries.constantCoeff T = 0 := by
            rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hTc]
            simp [hNpos, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0]
          have hTint : IntegralMv T := by
            intro e
            rw [hTc]
            split_ifs with he
            · exact ih e he
            · simp
          have hAg : Agree N h T := by
            intro e he
            rw [hTc, if_pos he]
          have hCD := hsub _ _ hCh (hP T hT0 hTint)
          have hLowD : Low N (f.subst h - f.subst T) := low_of_agree (agree_psubst f hh0 hT0 hAg)
          have hk := key f h0 h1 hh0 hT0 hAg d (by omega)
          have hb := hlowC _ hCD N hNpos hLowD d heq
          rw [map_sub, map_sub, map_sub, hTc, if_neg (by omega), sub_zero] at hk
          have hcd : MvPowerSeries.coeff d h = MvPowerSeries.coeff d (f.subst h - f.subst T) := by
            rw [map_sub]
            linear_combination -hk
          rw [hcd]
          exact hb
  intro d
  exact main (d.degree + 1) d (Nat.lt_succ_self _)

end Formalism.LT.InvIntP

theorem Formalism.LT.InvIntP.InvIntegralOfClass_proof : Formalism.LT.InvIntegralOfClass.{u, v} := by
  intro K _ _ ι _ C f h0 h1 hsub hP hlowC h hh0 hCh
  exact Formalism.LT.InvIntP.invIntegralOfClass K ι C f h0 h1 hsub hP hlowC h hh0 hCh

theorem Formalism.LT.InvIntP.FunEqLowCoeff_proof : Formalism.LT.FunEqLowCoeff.{u, v} := by
  intro K _ ι p q hq σ hq2 D hD N hN hlow d hd
  exact Formalism.LT.InvIntP.funEqLowCoeff p q hq σ hq2 D hD N hN hlow d hd

theorem Formalism.LT.InvIntP.IntegralSubst_proof : Formalism.LT.IntegralSubst.{u, v} := by
  intro K _ _ ι f P hf hP0 hP
  exact Formalism.LT.InvIntP.integralSubst f P hf hP0 hP

theorem Formalism.LT.InvIntegralOfClass_proof : Formalism.LT.InvIntegralOfClass.{u, v} := by
  exact Formalism.LT.InvIntP.InvIntegralOfClass_proof
theorem Formalism.LT.FunEqLowCoeff_proof : Formalism.LT.FunEqLowCoeff.{u, v} := by
  exact Formalism.LT.InvIntP.FunEqLowCoeff_proof
theorem Formalism.LT.IntegralSubst_proof : Formalism.LT.IntegralSubst.{u, v} := by
  exact Formalism.LT.InvIntP.IntegralSubst_proof
