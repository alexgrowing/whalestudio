import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjTheta0
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel

noncomputable section

namespace Formalism.L2.KerInert.Sigma

namespace ChartWirtingerDerivatives

open NumberField Formalism.BasicNotions

theorem qbar_iff (x : ℂ) : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar ↔ IsAlgebraic ℚ x := mem_algebraicClosure_iff

theorem qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
  (qbar_iff x).2 (IsAlgebraic.of_pow hn ((qbar_iff _).1 h))

theorem nat_mem (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  have h : ((n : ℕ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := natCast_mem _ n
  simpa using h

theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

theorem hasCMBy_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨-, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc.1 hδ0
  intro ω hω
  have h1 := hCM ω (by rw [← hL]; exact hω)
  rw [← hL] at h1
  have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
  rw [e]; exact h1

theorem disc_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem weierstrass_invariants_algebraic : InvAlg := by
  intro D cc δ hcc hδ L hL
  have hdisc := disc_curve D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) := Formalism.L2.Th1.CM.cm1 D.host.d L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) hcm
  have hjQ : Formalism.L2.Th1.CM.jInv L ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

end ChartWirtingerDerivatives

namespace ChartWirtingerDerivatives

open PowerSeries

def InQ (f : PowerSeries ℂ) : Prop := ∀ k, coeff k f ∈ Formalism.MainNotions.TaylorLogMetric.Qbar

theorem inQ_add {f g : PowerSeries ℂ} (hf : InQ f) (hg : InQ g) : InQ (f + g) := fun k => by
  rw [map_add]; exact add_mem (hf k) (hg k)

theorem inQ_neg {f : PowerSeries ℂ} (hf : InQ f) : InQ (-f) := fun k => by
  rw [map_neg]; exact neg_mem (hf k)

theorem inQ_sub {f g : PowerSeries ℂ} (hf : InQ f) (hg : InQ g) : InQ (f - g) := fun k => by
  rw [map_sub]; exact sub_mem (hf k) (hg k)

theorem inQ_mul {f g : PowerSeries ℂ} (hf : InQ f) (hg : InQ g) : InQ (f * g) := fun k => by
  rw [coeff_mul]; exact sum_mem fun p _ => mul_mem (hf _) (hg _)

theorem inQ_C {a : ℂ} (ha : a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : InQ (C a) := fun k => by
  rw [coeff_C]; split_ifs
  · exact ha
  · exact zero_mem _

theorem inQ_one : InQ 1 := by
  have : (1 : PowerSeries ℂ) = C 1 := by simp
  rw [this]; exact inQ_C (one_mem _)

theorem inQ_X : InQ X := fun k => by
  rw [coeff_X]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem inQ_pow {f : PowerSeries ℂ} (hf : InQ f) (n : ℕ) : InQ (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inQ_one
  | succ n ih => rw [pow_succ]; exact inQ_mul ih hf

theorem inQ_nsmul {f : PowerSeries ℂ} (hf : InQ f) (n : ℕ) : InQ (n • f) := fun k => by
  rw [map_nsmul]; exact nsmul_mem (hf k) n

theorem inQ_rescale {f : PowerSeries ℂ} (hf : InQ f) {a : ℂ} (ha : a ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) : InQ (rescale a f) := fun k => by
  rw [coeff_rescale]; exact mul_mem (pow_mem ha k) (hf k)

theorem inQ_dblInt {f : PowerSeries ℂ} (hf : InQ f) : InQ (Formalism.L2.Th1.C.dblInt f) := fun k => by
  unfold Formalism.L2.Th1.C.dblInt
  rw [coeff_mk]
  split_ifs
  · exact zero_mem _
  · exact div_mem (hf _) (mul_mem (natCast_mem _ k) (sub_mem (natCast_mem _ k) (one_mem _)))

theorem inQ_mvExp {f : PowerSeries ℂ} (hf : InQ f) (h0 : constantCoeff f = 0) :
    InQ (Formalism.L2.Th1.C.mvExp f : PowerSeries ℂ) := fun k => by
  have e : coeff k (Formalism.L2.Th1.C.mvExp f : PowerSeries ℂ)
      = MvPowerSeries.coeff (Finsupp.single () k) (Formalism.L2.Th1.C.mvExp f) := rfl
  rw [e, Formalism.L2.Th1.C.coeff_mvExp (f := f) h0 (N := k + 1) (by simp)]
  refine sum_mem fun j _ => mul_mem (inv_mem (natCast_mem _ _)) ?_
  exact inQ_pow hf j k

open Polynomial in

theorem tri_alg (n : ℕ) (b : ℕ → ℕ → ℂ) (hb : ∀ i k, b i k ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hb0 : ∀ i, b i 0 = 1) (q : ℕ → ℂ) (t : ℂ)
    (h : ∀ k ≤ n + 1, t ^ k / (k.factorial : ℂ) =
      ∑ i ∈ Finset.range (n + 1), q i * (if i ≤ k then b i (k - i) else 0)) :
    t ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  let V : ℕ → Submodule Formalism.MainNotions.TaylorLogMetric.Qbar ℂ := fun k => (degreeLE Formalism.MainNotions.TaylorLogMetric.Qbar (k : WithBot ℕ)).map (aeval t).toLinearMap
  have mono : ∀ j k, j ≤ k → V j ≤ V k := fun j k hjk =>
    Submodule.map_mono (degreeLE_mono (by exact_mod_cast hjk))
  have tpow : ∀ k, t ^ k ∈ V k := fun k =>
    Submodule.mem_map.2 ⟨Polynomial.X ^ k, mem_degreeLE.2 (degree_X_pow_le k), by simp⟩
  have smulc : ∀ {x : ℂ} {k : ℕ}, x ∈ V k → ∀ {c : ℂ}, c ∈ Formalism.MainNotions.TaylorLogMetric.Qbar → c * x ∈ V k := by
    intro x k hx c hc
    have e : c * x = ((⟨c, hc⟩ : Formalism.MainNotions.TaylorLogMetric.Qbar) • x) := rfl
    rw [e]; exact Submodule.smul_mem _ _ hx
  have hsum : ∀ k, k ≤ n + 1 → ∑ i ∈ Finset.range (n + 1), q i * (if i ≤ k then b i (k - i) else 0)
      = ∑ i ∈ Finset.range (min (k + 1) (n + 1)), q i * b i (k - i) := by
    intro k _
    have hsub : Finset.range (min (k + 1) (n + 1)) ⊆ Finset.range (n + 1) :=
      Finset.range_subset_range.2 (min_le_right _ _)
    rw [← Finset.sum_subset hsub (f := fun i => q i * (if i ≤ k then b i (k - i) else 0))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [if_pos (by omega)]
    · intro i hi hni
      simp only [Finset.mem_range] at hi hni
      rw [if_neg (by omega), mul_zero]
  have key : ∀ k, k ≤ n → q k ∈ V k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hk' := h k (by omega)
      rw [hsum k (by omega), show min (k + 1) (n + 1) = k + 1 by omega, Finset.sum_range_succ, Nat.sub_self,
        hb0, mul_one, div_eq_inv_mul] at hk'
      have e : q k = ((k.factorial : ℂ))⁻¹ * t ^ k - ∑ i ∈ Finset.range k, q i * b i (k - i) := by
        linear_combination (-1 : ℂ) * hk'
      rw [e]
      refine sub_mem (smulc (tpow k) (inv_mem (natCast_mem _ _))) (sum_mem fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      rw [mul_comm]
      exact smulc (mono i k (by omega) (ih i hi (by omega))) (hb i _)
  have hl := h (n + 1) le_rfl
  rw [hsum (n + 1) le_rfl, show min (n + 1 + 1) (n + 1) = n + 1 by omega] at hl
  have hmem : t ^ (n + 1) ∈ V n := by
    have e : t ^ (n + 1) = (((n + 1).factorial : ℕ) : ℂ) * ∑ i ∈ Finset.range (n + 1), q i * b i (n + 1 - i) := by
      have hf : (((n + 1).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [← hl]; field_simp
    rw [e]
    refine smulc (sum_mem fun i hi => ?_) (natCast_mem _ _)
    simp only [Finset.mem_range] at hi
    rw [mul_comm]
    exact smulc (mono i n (by omega) (key i (by omega))) (hb i _)
  obtain ⟨p, hp, hpt⟩ := Submodule.mem_map.1 hmem
  have hpd : p.degree ≤ n := mem_degreeLE.1 hp
  have hP : (Polynomial.X ^ (n + 1) - p : Formalism.MainNotions.TaylorLogMetric.Qbar[X]) ≠ 0 := by
    intro h0
    have e : (Polynomial.X ^ (n + 1) : Formalism.MainNotions.TaylorLogMetric.Qbar[X]) = p := sub_eq_zero.1 h0
    have h1 : (Polynomial.X ^ (n + 1) : Formalism.MainNotions.TaylorLogMetric.Qbar[X]).degree = ((n + 1 : ℕ) : WithBot ℕ) := degree_X_pow (n + 1)
    rw [e] at h1
    rw [h1] at hpd
    have : ((n + 1 : ℕ) : WithBot ℕ) ≤ (n : WithBot ℕ) := hpd
    norm_cast at this
    omega
  have halg : IsAlgebraic Formalism.MainNotions.TaylorLogMetric.Qbar t := ⟨Polynomial.X ^ (n + 1) - p, hP, by
    rw [map_sub, map_pow, aeval_X]
    have : (aeval t) p = t ^ (n + 1) := hpt
    rw [this, sub_self]⟩
  exact mem_algebraicClosure_iff.2
    (@IsAlgebraic.restrictScalars ℚ Formalism.MainNotions.TaylorLogMetric.Qbar ℂ _ _ _ _ _ _ _ _ (algebraicClosure.isAlgebraic ℚ ℂ) t halg)

theorem prod_expand {ι : Type} (A Y : PowerSeries ℂ) (s : Finset ι) (c : ι → ℂ) :
    ∃ q : ℕ → ℂ, ∏ i ∈ s, (A - C (c i) * Y) =
      ∑ i ∈ Finset.range (s.card + 1), C (q i) * Y ^ i * A ^ (s.card - i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, by simp⟩
  | insert a s ha ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨fun i => (if i ≤ s.card then q i else 0) - (if i = 0 then 0 else c a * q (i - 1)), ?_⟩
    rw [Finset.prod_insert ha, hq, Finset.card_insert_of_notMem ha]
    set m := s.card
    have e1 : ∑ i ∈ Finset.range (m + 1 + 1), C (if i ≤ m then q i else 0) * Y ^ i * A ^ (m + 1 - i)
        = A * ∑ i ∈ Finset.range (m + 1), C (q i) * Y ^ i * A ^ (m - i) := by
      rw [Finset.sum_range_succ, if_neg (by omega), map_zero, zero_mul, zero_mul, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [if_pos (by omega), show m + 1 - i = m - i + 1 by omega, pow_succ]
      ring
    have e2 : ∑ i ∈ Finset.range (m + 1 + 1), C (if i = 0 then 0 else c a * q (i - 1)) * Y ^ i * A ^ (m + 1 - i)
        = C (c a) * Y * ∑ i ∈ Finset.range (m + 1), C (q i) * Y ^ i * A ^ (m - i) := by
      rw [Finset.sum_range_succ', if_pos rfl, map_zero, zero_mul, zero_mul, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [if_neg (by omega), Nat.add_sub_cancel, show m + 1 - (i + 1) = m - i by omega, map_mul, pow_succ]
      ring
    have e3 : ∑ i ∈ Finset.range (m + 1 + 1),
        C ((if i ≤ m then q i else 0) - (if i = 0 then 0 else c a * q (i - 1))) * Y ^ i * A ^ (m + 1 - i)
        = ∑ i ∈ Finset.range (m + 1 + 1), C (if i ≤ m then q i else 0) * Y ^ i * A ^ (m + 1 - i)
          - ∑ i ∈ Finset.range (m + 1 + 1), C (if i = 0 then 0 else c a * q (i - 1)) * Y ^ i * A ^ (m + 1 - i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub]; ring
    rw [e3, e1, e2]
    ring

theorem rescale_C' (a c : ℂ) : rescale a (C c) = C c := by
  ext k
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

open Formalism.L2.Th1.C (mvExp mvExp_add mvExp_neg mvExp_nsmul mvExp_mul_neg rescale_mvExp coeff_mvExp constantCoeff_mvExp)

theorem coeff_mvExp_gauss (t : ℂ) (k : ℕ) :
    coeff (2 * k) (mvExp (C t * X ^ 2) : PowerSeries ℂ) = t ^ k / (k.factorial : ℂ) := by
  have h0 : MvPowerSeries.constantCoeff (C t * X ^ 2 : PowerSeries ℂ) = 0 := by
    change constantCoeff (C t * X ^ 2 : PowerSeries ℂ) = 0
    simp
  have e : coeff (2 * k) (mvExp (C t * X ^ 2) : PowerSeries ℂ)
      = MvPowerSeries.coeff (Finsupp.single () (2 * k)) (mvExp (C t * X ^ 2 : PowerSeries ℂ)) := rfl
  have ej : ∀ j, MvPowerSeries.coeff (Finsupp.single () (2 * k)) ((C t * X ^ 2 : PowerSeries ℂ) ^ j)
      = if 2 * k = 2 * j then t ^ j else 0 := by
    intro j
    have e2 : MvPowerSeries.coeff (Finsupp.single () (2 * k)) ((C t * X ^ 2 : PowerSeries ℂ) ^ j)
        = coeff (2 * k) ((C t * X ^ 2 : PowerSeries ℂ) ^ j) := rfl
    rw [e2, mul_pow, ← map_pow, ← pow_mul, coeff_C_mul_X_pow]
  rw [e, coeff_mvExp h0 (N := 2 * k + 1) (by rw [Finsupp.degree_single]; omega), Finset.sum_eq_single k]
  · rw [ej, if_pos rfl, div_eq_inv_mul]
  · intro j _ hj
    rw [ej, if_neg (by omega), mul_zero]
  · intro hk
    simp only [Finset.mem_range] at hk
    omega

theorem mul_s2_mem_Qbar_of_isogenyFormula (e : PowerSeries ℂ) (he : InQ e) (s α : ℂ) (hα : α ∈ Formalism.MainNotions.TaylorLogMetric.Qbar) (hα0 : α ≠ 0)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (hI : Formalism.L2.Th1.C.IsogenyFormula e s c α) :
    (((Fintype.card ι + 1 : ℕ) : ℂ) - α ^ 2) * s ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = Formalism.L2.Th1.C.dblInt e := ⟨_, rfl⟩
  obtain ⟨lm, hlm⟩ : ∃ lm, lm = Formalism.L2.Th1.C.lam e s := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : PowerSeries ℂ, Φ = mvExp (-lm) := ⟨_, rfl⟩
  obtain ⟨Pi, hPi⟩ : ∃ Pi : PowerSeries ℂ, Pi = ∏ P, Formalism.L2.Th1.C.wpShift e (c P) := ⟨_, rfl⟩
  have hD0 : constantCoeff D = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hD]
    unfold Formalism.L2.Th1.C.dblInt
    rw [coeff_mk]; simp
  have hlmD : lm = D + C (s / 2) * X ^ 2 := by rw [hlm, hD]; rfl
  have hlm0 : constantCoeff lm = 0 := by
    rw [hlmD, map_add, hD0, map_mul, map_pow, constantCoeff_X]; simp
  have hnl0 : constantCoeff (-lm) = 0 := by rw [map_neg, hlm0, neg_zero]

  have h1 : (rescale α Φ) ^ 2 = Φ ^ (2 * (n + 1)) * Pi := by
    have hI' := hI
    unfold Formalism.L2.Th1.C.IsogenyFormula Formalism.L2.Th1.C.sgStar at hI'
    rw [← hlm, ← hΦ, ← hPi, ← hn, map_mul, rescale_X] at hI'
    have hne : (C (α ^ 2) * X ^ (2 * n + 2) : PowerSeries ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ X_ne_zero)
      intro h0
      have := congrArg (coeff 0) h0
      rw [coeff_C, if_pos rfl, map_zero] at this
      exact hα0 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have key : C (α ^ 2) * X ^ (2 * n + 2) * ((rescale α Φ) ^ 2 - Φ ^ (2 * (n + 1)) * Pi) = 0 := by
      rw [map_pow] at hI' ⊢
      linear_combination hI'
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hne)

  have hr0 : constantCoeff (rescale α (-lm)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hnl0, mul_zero]
  have ha0 : constantCoeff ((2 * (n + 1)) • (-lm)) = 0 := by rw [map_nsmul, hnl0, smul_zero]
  have hna0 : constantCoeff (-((2 * (n + 1)) • (-lm))) = 0 := by rw [map_neg, ha0, neg_zero]
  have hb0 : constantCoeff (2 • rescale α (-lm)) = 0 := by rw [map_nsmul, hr0, smul_zero]
  have ha : (mvExp ((2 * (n + 1)) • (-lm)) : PowerSeries ℂ) = Φ ^ (2 * (n + 1)) := by
    rw [hΦ]; exact mvExp_nsmul hnl0 _
  have hb : (mvExp (2 • rescale α (-lm)) : PowerSeries ℂ) = (rescale α Φ) ^ 2 := by
    rw [hΦ, rescale_mvExp hnl0 α]; exact mvExp_nsmul hr0 2
  have h2 : Pi = mvExp (-((2 * (n + 1)) • (-lm)) + 2 • rescale α (-lm)) := by
    rw [mvExp_add hna0 hb0, hb, h1, ← ha, ← mul_assoc, mvExp_neg ha0, one_mul]

  set t : ℂ := (((2 * (n + 1) : ℕ) : ℂ)) * (s / 2) - 2 * (α ^ 2 * (s / 2)) with ht
  set F0 : PowerSeries ℂ := (2 * (n + 1)) • D - 2 • rescale α D with hF0
  have h3 : -((2 * (n + 1)) • (-lm)) + 2 • rescale α (-lm) = F0 + C t * X ^ 2 := by
    rw [hF0, ht, hlmD]
    simp only [map_neg, map_add, map_mul, map_pow, rescale_X, rescale_C', nsmul_eq_mul, map_sub, map_natCast]
    push_cast
    rw [show (C (2 : ℂ) : PowerSeries ℂ) = 2 from map_ofNat C 2]
    ring
  have hF00 : constantCoeff F0 = 0 := by
    rw [hF0, map_sub, map_nsmul, map_nsmul, hD0, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hD0]
    simp
  have hG0 : constantCoeff (C t * X ^ 2 : PowerSeries ℂ) = 0 := by simp
  have hnF0 : constantCoeff (-F0) = 0 := by rw [map_neg, hF00, neg_zero]
  have h4 : Pi * mvExp (-F0) = mvExp (C t * X ^ 2) := by
    rw [h2, h3, mvExp_add hF00 hG0, mul_comm (mvExp F0), mul_assoc, mvExp_mul_neg hF00, mul_one]

  have hw : ∀ x, Formalism.L2.Th1.C.wpShift e x = (1 + X ^ 2 * e) - C x * X ^ 2 := by
    intro x; unfold Formalism.L2.Th1.C.wpShift; ring
  obtain ⟨q, hq⟩ := prod_expand (1 + X ^ 2 * e) (X ^ 2) Finset.univ c
  rw [Finset.card_univ, ← hn] at hq
  have hPi' : Pi = ∑ i ∈ Finset.range (n + 1), C (q i) * (X ^ 2) ^ i * (1 + X ^ 2 * e) ^ (n - i) := by
    rw [hPi, ← hq]; simp only [hw]
  set B : ℕ → PowerSeries ℂ := fun i => (1 + X ^ 2 * e) ^ (n - i) * mvExp (-F0) with hB
  have h5 : mvExp (C t * X ^ 2) = ∑ i ∈ Finset.range (n + 1), C (q i) * (X ^ (2 * i) * B i) := by
    rw [← h4, hPi', Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB, pow_mul]; ring

  have hDq : InQ D := by rw [hD]; exact inQ_dblInt he
  have hF0q : InQ F0 := by rw [hF0]; exact inQ_sub (inQ_nsmul hDq _) (inQ_nsmul (inQ_rescale hDq hα) 2)
  have hAq : InQ (1 + X ^ 2 * e) := inQ_add inQ_one (inQ_mul (inQ_pow inQ_X 2) he)
  have hBq : ∀ i, InQ (B i) := fun i => inQ_mul (inQ_pow hAq _) (inQ_mvExp (inQ_neg hF0q) hnF0)
  have hB0 : ∀ i, coeff (2 * 0) (B i) = 1 := by
    intro i
    rw [mul_zero, coeff_zero_eq_constantCoeff_apply, hB]
    simp only [map_mul, map_pow, map_add, map_one, constantCoeff_X]
    have : constantCoeff (mvExp (-F0) : PowerSeries ℂ) = 1 := constantCoeff_mvExp hnF0
    rw [this]; simp
  have htri : t ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    refine tri_alg n (fun i k => coeff (2 * k) (B i)) (fun i k => hBq i _) hB0 q t ?_
    intro k _
    rw [← coeff_mvExp_gauss t k, h5, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_C_mul, coeff_X_pow_mul']
    congr 1
    by_cases hik : i ≤ k
    · rw [if_pos (by omega), if_pos hik, show 2 * k - 2 * i = 2 * (k - i) by omega]
    · rw [if_neg (by omega), if_neg hik]
  have e : (((Fintype.card ι + 1 : ℕ) : ℂ) - α ^ 2) * s = t := by
    rw [ht, ← hn]; push_cast; ring
  rw [e]; exact htri

theorem alpha_sq (dK : ℕ) :
    (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) ^ 2 = -(dK : ℂ) := by
  have h : (((Real.sqrt dK : ℝ) : ℂ)) ^ 2 = (dK : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) = Complex.I * ((Real.sqrt dK : ℝ) : ℂ) := by
    unfold Formalism.L2.Th1.CM.omegaK; push_cast; ring
  rw [e, mul_pow, h, Complex.I_sq]; ring

end ChartWirtingerDerivatives

open ChartWirtingerDerivatives

theorem invAlg' : InvAlg := ChartWirtingerDerivatives.weierstrass_invariants_algebraic

theorem secondEisensteinAlgebraic : SecondEisensteinAlgebraic := by
  intro D cc δ hcc hδ L hL
  obtain ⟨h2, h3⟩ := invAlg' D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d L hcm (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map Formalism.MainNotions.TaylorLogMetric.Qbar L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := mul_s2_mem_Qbar_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

end Formalism.L2.KerInert.Sigma
