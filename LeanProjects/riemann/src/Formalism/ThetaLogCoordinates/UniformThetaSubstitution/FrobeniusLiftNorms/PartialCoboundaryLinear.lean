import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)

namespace FrobeniusSubstitution

section Alg

variable {K : Type} [Field K]

theorem hasSubst_pair {κ : Type} {u v : MvPowerSeries κ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.HasSubst ![u, v] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp [hu, hv]

theorem hasSubst_frob {ι : Type} {p : ℕ} (hp : p ≠ 0) :
    MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X i : MvPowerSeries ι K) ^ p) := by
  exact MvPowerSeries.HasSubst.X_pow hp

theorem subst_psubst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    MvPowerSeries.subst b (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.subst b a) f := by
  first
    | exact MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb f
    | exact MvPowerSeries.subst_comp_subst_apply ha hb f
    | exact MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const_coeff ha) hb f

theorem subst_single_var {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    (x : ι) (f : PowerSeries K) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_psubst hb (PowerSeries.HasSubst.X x), MvPowerSeries.subst_X hb]

theorem frobVar_sub {ι : Type} {p : ℕ} (hp : p ≠ 0) (f g : MvPowerSeries ι K) :
    frobVar p (f - g) = frobVar p f - frobVar p g := by
  unfold frobVar
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_frob (K := K) (ι := ι) hp), map_sub]

theorem frobVar_add {ι : Type} {p : ℕ} (hp : p ≠ 0) (f g : MvPowerSeries ι K) :
    frobVar p (f + g) = frobVar p f + frobVar p g := by
  unfold frobVar
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_frob (K := K) (ι := ι) hp), map_add]

theorem frobVar_X {ι : Type} {p : ℕ} (hp : p ≠ 0) (i : ι) :
    frobVar p (MvPowerSeries.X i : MvPowerSeries ι K) = MvPowerSeries.X i ^ p := by
  exact MvPowerSeries.subst_X (hasSubst_frob hp) i

theorem constantCoeff_frobVar {ι : Type} {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K) :
    MvPowerSeries.constantCoeff (frobVar p f) = MvPowerSeries.constantCoeff f := by
  have e : frobVar p f = MvPowerSeries.expand p hp f := by
    first
      | rfl
      | (unfold frobVar; simp [MvPowerSeries.expand])
      | (unfold frobVar; rw [MvPowerSeries.expand_apply])
  rw [e, MvPowerSeries.constantCoeff_expand]

theorem frobVar_psubst {ι : Type} {p : ℕ} (hp : p ≠ 0) {a : MvPowerSeries ι K}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    frobVar p (PowerSeries.subst a f) = PowerSeries.subst (frobVar p a) f := by
  exact subst_psubst (hasSubst_frob hp) ha f

theorem frobVar_pair {κ : Type} {p : ℕ} (hp : p ≠ 0) {u v : MvPowerSeries κ K}
    (h : MvPowerSeries.HasSubst ![u, v]) (H : MvPowerSeries (Fin 2) K) :
    frobVar p (MvPowerSeries.subst ![u, v] H) =
      MvPowerSeries.subst ![frobVar p u, frobVar p v] H := by
  unfold frobVar
  rw [MvPowerSeries.subst_comp_subst_apply h (hasSubst_frob hp)]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem pair_frobVar {κ : Type} {p : ℕ} (hp : p ≠ 0) {u v : MvPowerSeries κ K}
    (h : MvPowerSeries.HasSubst ![u, v]) (H : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.subst ![u, v] (frobVar p H) = MvPowerSeries.subst ![u ^ p, v ^ p] H := by
  unfold frobVar
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_frob hp) h]
  congr 1
  funext s
  rw [← MvPowerSeries.coe_substAlgHom h, map_pow, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X h]
  fin_cases s <;> rfl

theorem map_pair {κ : Type} (σ : K →+* K) {u v : MvPowerSeries κ K}
    (h : MvPowerSeries.HasSubst ![u, v]) (H : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.map σ (MvPowerSeries.subst ![u, v] H) =
      MvPowerSeries.subst ![MvPowerSeries.map σ u, MvPowerSeries.map σ v]
        (MvPowerSeries.map σ H) := by
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem subst_g_zero_eq_log {ι : Type} {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {a : MvPowerSeries ι K}
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * PowerSeries.subst (a ^ p) (lgF K p) := by
  have hsXp : PowerSeries.HasSubst (PowerSeries.X ^ p : PowerSeries K) :=
    PowerSeries.HasSubst.X_pow (by omega)
  rw [(g_zero_relation_holds K p hp hpK).1, PowerSeries.subst_mul ha, PowerSeries.subst_C,
    PowerSeries.subst_comp_subst_apply hsXp ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

theorem subst_pow_g_zero {ι : Type} {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {a : MvPowerSeries ι K}
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst (a ^ p) (g0F K p) = PowerSeries.subst a (lgF K p) - a := by
  have hsXp : PowerSeries.HasSubst (PowerSeries.X ^ p : PowerSeries K) :=
    PowerSeries.HasSubst.X_pow (by omega)
  have h := congrArg (PowerSeries.subst a : PowerSeries K → MvPowerSeries ι K)
    (g_zero_relation_holds K p hp hpK).2
  rw [PowerSeries.subst_comp_subst_apply hsXp ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha,
    PowerSeries.subst_sub ha, PowerSeries.subst_X ha] at h
  exact h

theorem map_lgF (σ : K →+* K) (p : ℕ) : PowerSeries.map σ (lgF K p) = lgF K p := by
  ext n
  simp [lgF, map_sum, apply_ite]

theorem map_g0F (σ : K →+* K) (p : ℕ) : PowerSeries.map σ (g0F K p) = g0F K p := by
  ext n
  simp [g0F, map_sum, apply_ite]

theorem map_derivative (σ : K →+* K) (f : PowerSeries K) :
    PowerSeries.map σ (PowerSeries.derivative K f) =
      PowerSeries.derivative K (PowerSeries.map σ f) := by
  ext n
  simp [PowerSeries.coeff_derivative]

theorem map_inVar {ι : Type} (σ : K →+* K) (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map σ (at1 x f) = at1 x (PowerSeries.map σ f) := by
  unfold at1
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.X x), MvPowerSeries.map_X]

theorem map_pderiv {ι : Type} (σ : K →+* K) (x : ι) (f : MvPowerSeries ι K) :
    MvPowerSeries.map σ (MvPowerSeries.pderiv K x f) =
      MvPowerSeries.pderiv K x (MvPowerSeries.map σ f) := by
  ext n
  simp [MvPowerSeries.coeff_pderiv]

theorem pderiv_single_self {ι : Type} [Finite ι] (x : ι) (f : PowerSeries K) :
    MvPowerSeries.pderiv K x (at1 x f) = at1 x (PowerSeries.derivative K f) := by
  unfold at1
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X x) f x]
  first
    | rw [MvPowerSeries.pderiv_X_self, mul_one]
    | simp [MvPowerSeries.pderiv_X]

theorem pderiv_single_ne {ι : Type} [Finite ι] {x y : ι} (h : y ≠ x) (f : PowerSeries K) :
    MvPowerSeries.pderiv K x (at1 y f) = 0 := by
  unfold at1
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X y) f x]
  first
    | rw [MvPowerSeries.pderiv_X_of_ne h, mul_zero]
    | simp [MvPowerSeries.pderiv_X, h]

theorem pderiv_prod (k : K) (f g : PowerSeries K) :
    MvPowerSeries.pderiv K (0 : Fin 2) (MvPowerSeries.C k * (at1 0 f * at1 1 g)) =
      MvPowerSeries.C k * (at1 0 (PowerSeries.derivative K f) * at1 1 g) := by
  have hC : MvPowerSeries.pderiv K (0 : Fin 2) (MvPowerSeries.C k) = 0 := by
    ext n
    simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Derivation.leibniz, hC, pderiv_single_self, pderiv_single_ne h10, smul_zero, add_zero, zero_add,
    smul_eq_mul]
  ring

theorem partial_coboundary_linear {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0) (k q : K)
    (P G : MvPowerSeries (Fin 2) K) :
    d1 F (MvPowerSeries.C k * (P - MvPowerSeries.C q * G)) =
      MvPowerSeries.C k * (d1 F P - MvPowerSeries.C q * d1 F G) := by
  have h1 : MvPowerSeries.HasSubst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    MvPowerSeries.HasSubst.cons_subst_zero_left 0 1 2 hF0
  have h2 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    MvPowerSeries.HasSubst.X_X
  have h3 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    MvPowerSeries.HasSubst.X_X
  have hc : ∀ (ψ : MvPowerSeries (Fin 2) K →ₐ[K] MvPowerSeries (Fin 3) K) (a : K),
      ψ (MvPowerSeries.C a) = MvPowerSeries.C a := fun ψ a => by
    first
      | exact ψ.commutes a
      | (have h := ψ.commutes a; rwa [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h)
      | simp
  unfold d1
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2,
    ← MvPowerSeries.coe_substAlgHom h3]
  simp only [map_mul, map_sub, hc]
  ring

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sigma_le {p : ℕ} {σ : K →+* K}
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) (hp : 1 ≤ p) {a : K} (ha : ‖a‖ ≤ 1) :
    ‖σ a‖ ≤ 1 := by
  calc ‖σ a‖ = ‖(σ a - a ^ p) + a ^ p‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ p‖ ‖a ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ((hσ a ha).trans (inv_le_one_of_one_le₀ (by exact_mod_cast hp)))
        (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)

theorem integral_X {ι : Type} (i : ι) : Integral (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

end Norm

end FrobeniusSubstitution

open FrobeniusSubstitution in
theorem StepII_of (hW : DworkMv) (hD : DivDeriv) (hDe : DeIntegral) (hL : LawSymm) : StepII := by
  intro K _ _ _ p σ hU F hF G c _ hS hc hDer
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hσF : MvPowerSeries.map σ F = F := (hL K p hp hnp F hF).1 σ
  have hδi : Integral (cob F (g0F K p)) := hDe K p σ hp hnp hσ F hF
  obtain ⟨hF0, hFi, hFc⟩ := hF
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnp
    exact (inv_pos.mpr hppos).ne hnp
  have hinv : ‖((p : K)⁻¹)‖ = (p : ℝ) := by rw [norm_inv, hnp, inv_inv]
  have hscale : ∀ f : MvPowerSeries (Fin 3) K, Bd (p : ℝ)⁻¹ f →
      Integral (MvPowerSeries.C ((p : K)⁻¹) * f) := by
    intro f hf n
    rw [MvPowerSeries.coeff_C_mul, norm_mul, hinv]
    calc (p : ℝ) * ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hf n) hppos.le
      _ = 1 := mul_inv_cancel₀ hppos.ne'

  have hX0 : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => by simp
  have hXp0 : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ p) = 0 :=
    fun i => by simp [hp0]
  have hsX : ∀ i : Fin 3, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) :=
    fun i => PowerSeries.HasSubst.X i

  have hin3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] :=
    hasSubst_pair (hX0 0) (hX0 1)
  have hin3c : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hin3i : ∀ i : Fin 2, Integral
      (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] i) := fun i => by
    fin_cases i
    · exact integral_X 0
    · exact integral_X 1
  have hA0 : MvPowerSeries.constantCoeff (in3 F) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hin3 hin3c hF0
  have hAi : Integral (in3 F) := LogarithmEquivalence.integral_subst' hin3c hin3i hFi
  have hδ3i : Integral (in3 (cob F (g0F K p))) := LogarithmEquivalence.integral_subst' hin3c hin3i hδi
  have hσA : MvPowerSeries.map σ (in3 F) = in3 F := by
    unfold in3
    rw [map_pair σ hin3, hσF, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hsA : PowerSeries.HasSubst (in3 F) := PowerSeries.HasSubst.of_constantCoeff_zero hA0
  have hAp0 : MvPowerSeries.constantCoeff (in3 F ^ p) = 0 := by
    rw [map_pow, hA0, zero_pow hp0]
  have hfA0 : MvPowerSeries.constantCoeff (frobVar p (in3 F)) = 0 := by
    rw [constantCoeff_frobVar hp0, hA0]

  set r : MvPowerSeries (Fin 3) K :=
    MvPowerSeries.C ((p : K)⁻¹) * (frobVar p (in3 F) - in3 F ^ p) with hr
  have hCC : MvPowerSeries.C (p : K) * MvPowerSeries.C ((p : K)⁻¹) =
      (1 : MvPowerSeries (Fin 3) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpK, map_one]
  have hFr : frobVar p (in3 F) = in3 F ^ p + MvPowerSeries.C (p : K) * r := by
    rw [hr, ← mul_assoc, hCC]
    ring
  have hri : Integral r := by
    refine hscale _ fun n => ?_
    have h := frob_congr (σ := σ) hp hnp hσ (f := in3 F) hAi n
    rw [PhiH_apply, hσA, map_sub, norm_sub_rev, ← map_sub] at h
    exact h
  have hr0 : MvPowerSeries.constantCoeff r = 0 := by
    rw [hr, map_mul, map_sub, hfA0, hAp0, sub_zero, mul_zero]

  have h1 : MvPowerSeries.HasSubst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    hasSubst_pair hA0 (hX0 2)
  have h2 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    hasSubst_pair (hX0 0) (hX0 2)
  have h3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    hasSubst_pair (hX0 1) (hX0 2)
  set Gs : MvPowerSeries (Fin 2) K := MvPowerSeries.map σ G with hGs
  have hd1P : d1 F (frobVar p Gs) =
      MvPowerSeries.subst ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs := by
    unfold d1
    rw [pair_frobVar hp0 h1, pair_frobVar hp0 h2, pair_frobVar hp0 h3]
  have hd1s : frobVar p (MvPowerSeries.map σ (d1 F G)) =
      MvPowerSeries.subst ![frobVar p (in3 F),
        (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs := by
    unfold d1
    rw [map_sub, map_sub, map_pair σ h1, map_pair σ h2, map_pair σ h3, hσA, MvPowerSeries.map_X,
      MvPowerSeries.map_X, MvPowerSeries.map_X, frobVar_sub hp0, frobVar_sub hp0,
      frobVar_pair hp0 h1, frobVar_pair hp0 h2, frobVar_pair hp0 h3, frobVar_X hp0, frobVar_X hp0,
      frobVar_X hp0]

  have hE2 : Bd (p : ℝ)⁻¹ (frobVar p (MvPowerSeries.map σ (d1 F G)) -
      MvPowerSeries.C (p : K) * d1 F G) := by
    obtain ⟨hS0, hS1⟩ := hS
    rw [sub_zero] at hS0 hS1
    exact (hW K (Fin 3) p σ hp hnp hσ (d1 F G) hS0).1 hS1

  set Φ : MvPowerSeries (Fin 2) K :=
    Gs - MvPowerSeries.C (σ c) * (at1 0 (lgF K p) * at1 1 (g0F K p)) with hΦ
  have hΦi : Integral (MvPowerSeries.pderiv (R := K) 0 Φ) := by
    have e : MvPowerSeries.pderiv (R := K) 0 Φ = MvPowerSeries.map σ
        (MvPowerSeries.pderiv (R := K) 0 G -
          MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) := by
      rw [hΦ, map_sub, pderiv_prod, map_sub, map_mul, map_mul, MvPowerSeries.map_C, map_inVar,
        map_inVar, map_derivative, map_lgF, map_g0F, map_pderiv]
    rw [e]
    intro n
    rw [MvPowerSeries.coeff_map]
    exact norm_sigma_le hσ hp.one_le (hDer n)
  have hE1 := hD K (Fin 2) (Fin 3) p hp hnp 0 Φ
    ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] r hΦi
    (fun i => by
      fin_cases i
      · exact hAp0
      · exact hXp0 2)
    (fun i => by
      fin_cases i
      · exact int_pow hAi p
      · exact int_pow (integral_X 2) p) hr0 hri
  have hupd : Function.update ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] 0
      (![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] 0 +
        MvPowerSeries.C (p : K) * r) =
      ![frobVar p (in3 F), (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] := by
    funext i
    fin_cases i
    · simp [hFr]
    · simp
  rw [hupd] at hE1
  have hSΦ : ∀ u v : MvPowerSeries (Fin 3) K, MvPowerSeries.HasSubst ![u, v] →
      MvPowerSeries.subst ![u, v] Φ = MvPowerSeries.subst ![u, v] Gs -
        MvPowerSeries.C (σ c) *
          (PowerSeries.subst u (lgF K p) * PowerSeries.subst v (g0F K p)) := by
    intro u v h
    rw [hΦ, MvPowerSeries.subst_sub h, MvPowerSeries.subst_mul h, MvPowerSeries.subst_mul h,
      MvPowerSeries.subst_C, subst_single_var h, subst_single_var h]
    rfl

  have hlog : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) := by
    unfold cob at hFc
    linear_combination hFc
  have hsF : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hlogA : PowerSeries.subst (in3 F) (lgF K p) =
      (at1 0 (lgF K p) + at1 1 (lgF K p) : MvPowerSeries (Fin 3) K) := by
    have h := congrArg in3 hlog
    unfold in3 at h ⊢
    rw [subst_psubst hin3 hsF, MvPowerSeries.subst_add hin3, subst_single_var hin3, subst_single_var hin3] at h
    exact h
  have hat : ∀ i : Fin 3, at1 i (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * frobVar p (at1 i (lgF K p)) := fun i => by
    unfold at1
    rw [subst_g_zero_eq_log hp2 hpK (hsX i), frobVar_psubst hp0 (hsX i), frobVar_X hp0]
  have hδ : in3 (cob F (g0F K p)) = MvPowerSeries.C ((p : K)⁻¹) *
      (PowerSeries.subst (in3 F ^ p) (lgF K p) -
        PowerSeries.subst (frobVar p (in3 F)) (lgF K p)) := by
    have e : in3 (cob F (g0F K p)) =
        PowerSeries.subst (in3 F) (g0F K p) - at1 0 (g0F K p) - at1 1 (g0F K p) := by
      unfold cob in3
      rw [MvPowerSeries.subst_sub hin3, MvPowerSeries.subst_sub hin3, subst_psubst hin3 hsF,
        subst_single_var hin3, subst_single_var hin3]
      rfl
    rw [e, subst_g_zero_eq_log hp2 hpK hsA, hat, hat, ← frobVar_psubst hp0 hsA, hlogA, frobVar_add hp0]
    ring
  have hgb : PowerSeries.subst ((MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p) (g0F K p) =
      at1 2 (lgF K p) - MvPowerSeries.X 2 := subst_pow_g_zero hp2 hpK (hsX 2)

  have key : d1 F (DeS p σ G) -
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) =
      MvPowerSeries.C ((p : K)⁻¹) *
        ((frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G) -
          (MvPowerSeries.subst ![frobVar p (in3 F),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
            MvPowerSeries.subst ![in3 F ^ p,
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ)) -
        MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * MvPowerSeries.X 2) := by
    unfold DeS
    rw [partial_coboundary_linear hF0, hd1P, hd1s, hSΦ _ _ (hasSubst_pair hfA0 (hXp0 2)),
      hSΦ _ _ (hasSubst_pair hAp0 (hXp0 2)), hgb, hδ]
    ring
  rw [key]
  exact bd_sub (hscale _ (bd_sub hE2 hE1))
    (int_mul (bd_C zero_le_one (norm_sigma_le hσ hp.one_le hc)) (int_mul hδ3i (integral_X 2)))

end Formalism.InvariantFactorPaths.G7
