import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff

namespace GlobalTheory.HWL.SeriesEval

open PowerSeries IsLocalRing Filter Topology

section Shift

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem X_add_C_mem {c : O} (hc : c ∈ maximalIdeal O) : (X + C c : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simpa using hc

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem exists_shift {c : O} (hc : c ∈ maximalIdeal O) :
    ∃ s : O⟦X⟧ →ₐ[O] O⟦X⟧, s X = X + C c := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  exact ⟨GlobalTheory.mvEvalAdic (σ := Unit) O (maximalIdeal O⟦X⟧) (fun _ => X + C c)
    (fun _ => X_add_C_mem hc), GlobalTheory.mvEvalAdic_X (σ := Unit) _ _ _ ()⟩

theorem exists_div {c : O} (hc : c ∈ maximalIdeal O) (b : O⟦X⟧) :
    ∃ (r : O) (q : O⟦X⟧), b = C r + (X - C c) * q := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  obtain ⟨s, hs⟩ := exists_shift hc
  obtain ⟨s', hs'⟩ := exists_shift (neg_mem hc)
  have hC : ∀ r, s' (C r) = C r := fun r => s'.commutes r
  have hX : (s'.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add, hs', hC, map_neg]; ring
  have h : s'.comp s = AlgHom.id O O⟦X⟧ :=
    GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (σ := Unit) (maximalIdeal O⟦X⟧)
      (fun _ => by
        change (s'.comp s) X ∈ _
        rw [hX]; simpa using X_add_C_mem (zero_mem (maximalIdeal O)))
      (fun _ => hX)
  refine ⟨constantCoeff (s b), s' (mk fun p => coeff (p + 1) (s b)), ?_⟩
  have h1 : s' (s b) = b := DFunLike.congr_fun h b
  conv_lhs => rw [← h1, eq_X_mul_shift_add_const (s b)]
  rw [map_add, map_mul, hs', hC, map_neg]
  ring

variable {L : Type*} [CommRing L] [Algebra O L]

theorem exists_ev {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) : ∃ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x := by
  obtain ⟨s, hs⟩ := exists_shift hc
  have hy : HasSubst (x - C (algebraMap O L c)) :=
    HasSubst.of_constantCoeff_zero' (by simp [hx])
  refine ⟨(substAlgHom hy).comp s, ?_⟩
  have hC : (substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧) (C c) = C (algebraMap O L c) :=
    ((substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧).commutes c).trans (PowerSeries.algebraMap_apply (r := c))
  rw [AlgHom.comp_apply, hs, map_add, substAlgHom_X, hC]
  ring

theorem ev_div {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) :
    ∃ z : L⟦X⟧, ∀ b : O⟦X⟧, ∃ (r : O) (q : O⟦X⟧), ∀ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x →
      ev b = C (algebraMap O L r) + X * (z * ev q) := by
  refine ⟨mk fun p => coeff (p + 1) x, fun b => ?_⟩
  obtain ⟨r, q, rfl⟩ := exists_div hc b
  refine ⟨r, q, fun ev hev => ?_⟩
  have hC : ∀ r, ev (C r) = C (algebraMap O L r) := fun r =>
    (ev.commutes r).trans PowerSeries.algebraMap_apply
  rw [map_add, map_mul, map_sub, hC, hC, hev, ← hx, ← mul_assoc]
  congr 2
  rw [sub_eq_iff_eq_add]
  exact eq_X_mul_shift_add_const x

theorem ev_unique {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) (ev ev' : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (h' : ev' X = x) : ev = ev' := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  have key : ∀ (k : ℕ) (b : O⟦X⟧), X ^ k ∣ ev b - ev' b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b
      obtain ⟨r, q, hq⟩ := hz b
      have : ev b - ev' b = X * (z * (ev q - ev' q)) := by rw [hq ev h, hq ev' h']; ring
      rw [this, pow_succ']
      exact mul_dvd_mul_left _ ((ih q).mul_left z)
  refine AlgHom.ext fun b => PowerSeries.ext fun k => ?_
  have := X_pow_dvd_iff.1 (key (k + 1) b) k k.lt_succ_self
  rwa [map_sub, sub_eq_zero] at this

variable {K : Type*} [NormedField K] (i : L →+* K)

theorem ev_bounded (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (k : ℕ) : ∃ B : ℝ, ∀ b, ‖i (coeff k (ev b))‖ ≤ B := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · refine ⟨1, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      simpa [hq ev h] using hi r
    · choose! B hB using ih
      refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ‖i (coeff p.1 z)‖ * B p.2, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      rw [hq ev h, map_add, coeff_succ_X_mul, coeff_C, if_neg k.succ_ne_zero, zero_add, coeff_mul,
        map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      rw [map_mul, norm_mul]
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact mul_le_mul_of_nonneg_left (hB _ (by omega) _) (norm_nonneg _)

theorem ev_tendsto (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (hc1 : ‖i (algebraMap O L c)‖ < 1)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (a : O⟦X⟧) (k : ℕ) :
    Tendsto (fun m : ℕ => i (coeff k (ev ((trunc m a : Polynomial O) : O⟦X⟧)))) atTop
      (𝓝 (i (coeff k (ev a)))) := by
  obtain ⟨B, hB⟩ := ev_bounded i hi hc x hx ev h k
  have hC : ev (C c) = C (algebraMap O L c) := (ev.commutes c).trans PowerSeries.algebraMap_apply
  rw [← tendsto_add_atTop_iff_nat k, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun n => ‖i (algebraMap O L c)‖ ^ n * B)
    (fun n => ?_) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hc1).mul_const B)
  obtain ⟨b, hb⟩ : X ^ (n + k) ∣ ((trunc (n + k) a : Polynomial O) : O⟦X⟧) - a :=
    X_pow_dvd_iff.2 fun m hm => by simp [coeff_trunc, hm]
  have hmem : (C c + (X - C c) : O⟦X⟧) ^ (n + (k + 1) - 1) ∈
      Ideal.span {C c ^ n, (X - C c) ^ (k + 1)} :=
    Ideal.add_pow_add_pred_mem_of_pow_mem_of_commute _
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) (Commute.all _ _)
  rw [add_sub_cancel, show n + (k + 1) - 1 = n + k by omega, Ideal.mem_span_pair] at hmem
  obtain ⟨u, v, huv⟩ := hmem
  have hy : X ∣ x - C (algebraMap O L c) := X_dvd_iff.2 (by simp [hx])
  have h0 : coeff k ((x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b)) = 0 :=
    X_pow_dvd_iff.1 ((pow_dvd_pow_of_dvd hy _).mul_right _) k k.lt_succ_self
  have he : ev (X ^ (n + k) * b) = C (algebraMap O L c ^ n) * ev (u * b) +
      (x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b) := by
    rw [← huv]
    simp only [map_mul, map_add, map_pow, map_sub, hC, h]
    ring
  rw [← map_sub, ← map_sub, ← map_sub, hb, he, map_add, h0, add_zero, coeff_C_mul, map_mul,
    norm_mul, map_pow, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

end Shift

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem existsUnique_ev : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (x : PowerSeries ↥LL.1),
    ‖((PowerSeries.constantCoeff x : ↥LL.1) : Om l)‖ < 1 →
    (∃! ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x) ∧
    ∀ ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x →
      ∀ (a : PowerSeries ↥(OL LL)) (k : ℕ), Filter.Tendsto (fun m : ℕ =>
        ((PowerSeries.coeff k (ev ((PowerSeries.trunc m a : Polynomial ↥(OL LL)) :
          PowerSeries ↥(OL LL))) : ↥LL.1) : Om l)) Filter.atTop
        (nhds ((PowerSeries.coeff k (ev a) : ↥LL.1) : Om l)) := by
  intro l _ LL x hx
  obtain ⟨_, hcomp, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hfin := LL.2
  have hn : ∀ y : ↥LL.1, ‖GlobalTheory.DiscEval.fieldEmb LL.1 y‖ = ‖(y : Om l)‖ := fun y => by
    rw [GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hi : ∀ r : ↥(OL LL), ‖algebraMap ↥LL.1 (Om l) (algebraMap ↥(OL LL) ↥LL.1 r)‖ ≤ 1 :=
    fun r => (hn r).ge.trans ((GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 r).1 r.2)
  let c : ↥(OL LL) := ⟨constantCoeff x,
    (GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 _).2 ((hn _).trans_le hx.le)⟩
  have hxc : constantCoeff x = algebraMap ↥(OL LL) ↥LL.1 c := rfl
  have hc : c ∈ maximalIdeal ↥(OL LL) := fun hu =>
    ((hn _).trans_lt hx).ne ((GlobalTheory.DiscEval.isUnit_iff_norm LL.1 c).1 hu)
  have hinst : ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = MvPowerSeries.instAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      (PowerSeries.algebraMap_apply (R := ↥(OL LL)) (A := ↥LL.1) (r := r)).symm
  generalize ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = inst at hinst ⊢
  subst hinst
  refine ⟨?_, fun ev hev a k =>
    ev_tendsto (algebraMap ↥LL.1 (Om l)) hi hc hx x hxc ev hev a k⟩
  obtain ⟨ev, hev⟩ := exists_ev hc x hxc
  exact ⟨ev, hev, fun ev' hev' => ev_unique hc x hxc ev' ev hev' hev⟩

end GlobalTheory.HWL.SeriesEval
