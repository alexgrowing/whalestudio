import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementH
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)

theorem mfact_zero {ι : Type} : mfact (0 : ι →₀ ℕ) = 1 := by
  simp [mfact]

theorem mfact_single_one {ι : Type} (i : ι) : mfact (Finsupp.single i 1) = 1 := by
  unfold mfact
  rw [Finsupp.prod_single_index] <;> rfl

theorem mfact_mul_dvd_add {ι : Type} (μ ν : ι →₀ ℕ) : mfact μ * mfact ν ∣ mfact (μ + ν) := by
  classical
  have key : ∀ κ : ι →₀ ℕ, κ.support ⊆ μ.support ∪ ν.support →
      mfact κ = ∏ i ∈ μ.support ∪ ν.support, (κ i).factorial := by
    intro κ hκ
    exact Finsupp.prod_of_support_subset κ hκ (fun _ k => k.factorial) (fun _ _ => rfl)
  rw [key μ Finset.subset_union_left, key ν Finset.subset_union_right,
    key (μ + ν) Finsupp.support_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => by
    rw [Finsupp.add_apply]
    exact Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem jets_in_norm_holds : JetsInNorm := by
  intro K _ _ ι f
  first
    | exact Iff.rfl
    | exact forall_congr' (fun κ => by simp [Formalism.G.unitBall])

section Ring

variable {K : Type} [Field K] {R : Subring K} {ι : Type}

theorem jetsIn_of_int {f : MvPowerSeries ι K} (hf : Formalism.L2.Th1.C.IntMv R f) : JetsIn R f := fun κ => R.mul_mem (natCast_mem R _) (hf κ)

theorem jetsIn_C {c : K} (hc : c ∈ R) : JetsIn R (MvPowerSeries.C c : MvPowerSeries ι K) := by
  intro κ
  classical
  by_cases h : κ = 0
  · subst h
    simpa [mfact_zero] using hc
  · simp [MvPowerSeries.coeff_C, h]

theorem jetsIn_one : JetsIn R (1 : MvPowerSeries ι K) := by
  have h := jetsIn_C (ι := ι) (R := R) (c := 1) R.one_mem
  rwa [map_one] at h

theorem jetsIn_X (i : ι) : JetsIn R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  intro κ
  classical
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h
    simp [mfact_single_one]
  · simp

theorem jetsIn_add {f g : MvPowerSeries ι K} (hf : JetsIn R f) (hg : JetsIn R g) :
    JetsIn R (f + g) := by
  intro κ
  rw [map_add, mul_add]
  exact R.add_mem (hf κ) (hg κ)

theorem jetsIn_neg {f : MvPowerSeries ι K} (hf : JetsIn R f) : JetsIn R (-f) := by
  intro κ
  rw [map_neg, mul_neg]
  exact R.neg_mem (hf κ)

theorem jetsIn_mul {f g : MvPowerSeries ι K} (hf : JetsIn R f) (hg : JetsIn R g) :
    JetsIn R (f * g) := by
  classical
  intro κ
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine sum_mem (fun p hp => ?_)
  have hp' : p.1 + p.2 = κ := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | simpa using hp
  obtain ⟨q, hq⟩ := mfact_mul_dvd_add p.1 p.2
  rw [← hp', hq]
  have e : ((mfact p.1 * mfact p.2 * q : ℕ) : K) *
      (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) =
      (q : K) * (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 f) *
        (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 g) := by
    push_cast
    ring
  rw [e]
  exact R.mul_mem (R.mul_mem (natCast_mem R q) (hf p.1)) (hg p.2)

theorem jetsIn_sum {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K)
    (hf : ∀ a ∈ s, JetsIn R (f a)) : JetsIn R (∑ a ∈ s, f a) := by
  exact Finset.sum_induction f (JetsIn R) (fun a b ha hb => jetsIn_add ha hb)
    (by simpa using jetsIn_C (ι := ι) (R := R) R.zero_mem) hf

theorem jetsIn_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K)
    (hf : ∀ a ∈ s, JetsIn R (f a)) : JetsIn R (∏ a ∈ s, f a) := by
  exact Finset.prod_induction f (JetsIn R) (fun a b ha hb => jetsIn_mul ha hb)
    jetsIn_one hf

theorem jetsIn_pow {f : MvPowerSeries ι K} (hf : JetsIn R f) (n : ℕ) : JetsIn R (f ^ n) := by
  induction n with
  | zero => simpa using (jetsIn_one (R := R) (ι := ι))
  | succ n ih => rw [pow_succ]; exact jetsIn_mul ih hf

theorem jet_pderiv (f : MvPowerSeries ι K) (i : ι) (κ : ι →₀ ℕ) :
    ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (MvPowerSeries.pderiv K i f) =
      ((mfact (κ + Finsupp.single i 1) : ℕ) : K) *
        MvPowerSeries.coeff (κ + Finsupp.single i 1) f := by
  rw [mfact_add_single, MvPowerSeries.coeff_pderiv]
  push_cast
  ring

theorem jetsIn_pderiv {f : MvPowerSeries ι K} (hf : JetsIn R f) (i : ι) :
    JetsIn R (MvPowerSeries.pderiv K i f) := by
  intro κ
  rw [jet_pderiv]
  exact hf _

theorem jetsIn_iff_pderiv (f : MvPowerSeries ι K) :
    JetsIn R f ↔ MvPowerSeries.constantCoeff f ∈ R ∧
      ∀ i, JetsIn R (MvPowerSeries.pderiv K i f) := by
  constructor
  · intro hf
    refine ⟨?_, fun i => jetsIn_pderiv hf i⟩
    simpa [mfact_zero] using hf 0
  · rintro ⟨h0, hd⟩ κ
    classical
    by_cases hκ : κ = 0
    · subst hκ
      simpa [mfact_zero] using h0
    · obtain ⟨i, hi⟩ : ∃ i, κ i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hκ (Finsupp.ext h)
      have hk : κ - Finsupp.single i 1 + Finsupp.single i 1 = κ :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
      have h := hd i (κ - Finsupp.single i 1)
      rw [jet_pderiv, hk] at h
      exact h

end Ring

theorem jets_ring_holds : JetsRing := by
  intro K _ R ι
  exact ⟨fun c hc => jetsIn_C hc, jetsIn_X, fun f g => jetsIn_add, fun f => jetsIn_neg,
    fun f g => jetsIn_mul⟩

theorem integral_jets_holds : IntJets := by
  intro K _ R ι f hf
  exact jetsIn_of_int hf

theorem jets_deriv_holds : JetsDeriv := by
  intro K _ R ι f
  exact jetsIn_iff_pderiv f

section CharZero

variable {K : Type} [Field K] [CharZero K] {R : Subring K} {ι : Type}

theorem pderiv_divPow (a : MvPowerSeries ι K) (i : ι) (m : ℕ) :
    MvPowerSeries.pderiv K i (MvPowerSeries.C (((m + 1).factorial : K)⁻¹) * a ^ (m + 1)) =
      (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m) * MvPowerSeries.pderiv K i a := by
  have hC : ∀ c : K, MvPowerSeries.pderiv K i (MvPowerSeries.C c : MvPowerSeries ι K) = 0 := by
    intro c
    have h := (MvPowerSeries.pderiv K i : Derivation K (MvPowerSeries ι K) (MvPowerSeries ι K)).map_algebraMap c
    simpa [MvPowerSeries.algebraMap_apply] using h
  have hN : ((m + 1 : ℕ) : MvPowerSeries ι K) = MvPowerSeries.C ((m + 1 : ℕ) : K) :=
    (map_natCast _ _).symm
  have h1 : ((m : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have h2 : ((m.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have key : (((m + 1).factorial : K))⁻¹ * ((m + 1 : ℕ) : K) = ((m.factorial : K))⁻¹ := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [Derivation.leibniz, hC, smul_zero, add_zero, Derivation.leibniz_pow, Nat.add_sub_cancel,
    smul_eq_mul, nsmul_eq_mul, smul_eq_mul, hN, ← key, map_mul]
  ring

theorem jetsIn_divPow {a : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff a = 0)
    (ha : JetsIn R a) (m : ℕ) : JetsIn R (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m) := by
  induction m with
  | zero => simpa using (jetsIn_one (R := R) (ι := ι))
  | succ m ih =>
    rw [jetsIn_iff_pderiv]
    refine ⟨?_, fun i => ?_⟩
    · simp [h0]
    · rw [pderiv_divPow]
      exact jetsIn_mul ih (jetsIn_pderiv ha i)

theorem coeff_subst_one (f : PowerSeries K) {a : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff a = 0) {n : ι →₀ ℕ} {N : ℕ} (hN : n.degree < N) :
    MvPowerSeries.coeff n (PowerSeries.subst a f) =
      ∑ k ∈ range N, PowerSeries.coeff k f * MvPowerSeries.coeff n (a ^ k) := by
  classical
  rw [PowerSeries.coeff_subst (Formalism.L2.Th1.C.hasSubst_of_cc h0),
    finsum_eq_sum_of_support_subset (s := range N)]
  · exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    rw [Formalism.L2.Th1.C.coeff_pow_eq_zero_of_cc h0 (by omega), smul_zero]

theorem jetsIn_subst_one {f : PowerSeries K} {a : MvPowerSeries ι K} (hf : JetsIn1 R f)
    (h0 : MvPowerSeries.constantCoeff a = 0) (ha : JetsIn R a) :
    JetsIn R (PowerSeries.subst a f) := by
  intro n
  rw [coeff_subst_one f h0 (Nat.lt_succ_self n.degree), Finset.mul_sum]
  refine sum_mem (fun k _ => ?_)
  have hk : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have e : ((mfact n : ℕ) : K) * (PowerSeries.coeff k f * MvPowerSeries.coeff n (a ^ k)) =
      (((k.factorial : ℕ) : K) * PowerSeries.coeff k f) *
        (((mfact n : ℕ) : K) *
          MvPowerSeries.coeff n (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k)) := by
    rw [MvPowerSeries.coeff_C_mul]
    calc _ = (((mfact n : ℕ) : K) * (PowerSeries.coeff k f * MvPowerSeries.coeff n (a ^ k))) *
          (((k.factorial : ℕ) : K) * ((k.factorial : K))⁻¹) := by rw [mul_inv_cancel₀ hk, mul_one]
      _ = _ := by ring
  rw [e]
  exact R.mul_mem (hf k) (jetsIn_divPow h0 ha k n)

theorem jetsIn1_exp : JetsIn1 R (PowerSeries.exp K) := by
  intro n
  have hn : ((n.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have e : ((n.factorial : ℕ) : K) * PowerSeries.coeff n (PowerSeries.exp K) = 1 := by
    simp [PowerSeries.coeff_exp, hn]
  rw [e]
  exact R.one_mem

theorem jetsIn_mvExp {a : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff a = 0)
    (ha : JetsIn R a) : JetsIn R (Formalism.L2.Th1.C.mvExp a) := jetsIn_subst_one jetsIn1_exp h0 ha

end CharZero

theorem jets_div_pow_holds : JetsDivPow := by
  intro K _ _ R ι a h0 ha m
  exact jetsIn_divPow h0 ha m

theorem jets_subst_one_holds : JetsSubstOne := by
  intro K _ _ R ι f a hf h0 ha
  exact jetsIn_subst_one hf h0 ha

theorem jets_exp_holds : JetsExp := by
  intro K _ _ R ι a h0 ha
  exact jetsIn_mvExp h0 ha

end Formalism.L2.Th1.G
