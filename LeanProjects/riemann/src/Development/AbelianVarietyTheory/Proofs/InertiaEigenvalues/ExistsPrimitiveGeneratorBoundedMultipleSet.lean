import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.GcdGen

variable {K : Type} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => Valuation.valuationSubring (NormedField.valuation (K := K))

theorem mem_ball (x : K) : x ∈ 𝒪 ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem mem_span_pow (a x : 𝒪) (n : ℕ) :
    x ∈ (Ideal.span {a}) ^ n ↔ ‖(x : K)‖ ≤ ‖(a : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    have hy : ‖(y : K)‖ ≤ 1 := (mem_ball _).1 y.2
    have e : ((y * a ^ n : 𝒪) : K) = (y : K) * (a : K) ^ n := by push_cast; ring
    rw [e, norm_mul, norm_pow]
    calc ‖(y : K)‖ * ‖(a : K)‖ ^ n ≤ 1 * ‖(a : K)‖ ^ n :=
          mul_le_mul_of_nonneg_right hy (by positivity)
      _ = _ := one_mul _
  · intro hx
    by_cases ha : (a : K) ^ n = 0
    · have hx0 : (x : K) = 0 := by
        rw [← norm_le_zero_iff]; rw [← norm_pow, ha, norm_zero] at hx; exact hx
      refine ⟨0, Subtype.ext ?_⟩
      simp [hx0]
    · refine ⟨⟨(x : K) / (a : K) ^ n, (mem_ball _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div, norm_pow]; exact div_le_one_of_le₀ hx (by positivity)
      · show (x : K) / (a : K) ^ n * ((a ^ n : 𝒪) : K) = x
        push_cast
        field_simp

theorem isAdicComplete_span [CompleteSpace K] (a : 𝒪) (ha : ‖(a : K)‖ < 1) :
    IsAdicComplete (Ideal.span {a}) 𝒪 := by
  have key : ∀ (n : ℕ) (x y : 𝒪), x ≡ y [SMOD (Ideal.span {a}) ^ n • (⊤ : Submodule 𝒪 𝒪)] ↔
      ‖(x : K) - y‖ ≤ ‖(a : K)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]
    push_cast; rfl
  have h0 := norm_nonneg (a : K)
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · have hle : ∀ n : ℕ, ‖(x : K)‖ ≤ ‖(a : K)‖ ^ n := fun n => by
      simpa using (key n x 0).1 (hx n)
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one h0 ha
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht hle
    exact Subtype.ext (by simpa using this)
  · have hC : ∀ {m n : ℕ}, m ≤ n → ‖(f m : K) - f n‖ ≤ ‖(a : K)‖ ^ m := fun h =>
      (key _ _ _).1 (hf h)
    have hcs : CauchySeq (fun n => (f n : K)) := by
      refine cauchySeq_of_le_geometric ‖(a : K)‖ 1 ha fun n => ?_
      rw [dist_eq_norm, one_mul]; exact hC (Nat.le_succ n)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => (mem_ball _).1 (f n).2
    refine ⟨⟨L, (mem_ball _).2 hL1⟩, fun n => (key _ _ _).2 ?_⟩
    show ‖(f n : K) - L‖ ≤ _
    have ht : Filter.Tendsto (fun m => ‖(f n : K) - f m‖) Filter.atTop
        (nhds ‖(f n : K) - L‖) := (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => hC hm⟩)

theorem isUnit_of_norm_eq_one (x : 𝒪) (hx : ‖(x : K)‖ = 1) : IsUnit x := by
  have hx0 : (x : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
  refine IsUnit.of_mul_eq_one (⟨(x : K)⁻¹, (mem_ball _).2 (by rw [norm_inv, hx, inv_one])⟩ : 𝒪) ?_
  exact Subtype.ext (by simp [hx0])

end GlobalTheory.GcdGen

namespace GlobalTheory.GcdGen

variable {K : Type} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => Valuation.valuationSubring (NormedField.valuation (K := K))

theorem wdiv [CompleteSpace K] (g h : K⟦X⟧) (d : ℕ) (hg1 : ∀ n, ‖coeff n g‖ ≤ 1)
    (hgd : ‖coeff d g‖ = 1) (hlt : ∀ n < d, ‖coeff n g‖ < 1) (hh : ∀ n, ‖coeff n h‖ ≤ 1) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ (∀ n, ‖coeff n r‖ ≤ 1) ∧
      (∀ n, d ≤ n → coeff n r = 0) ∧ h = g * q + r := by
  classical
  let ι : 𝒪 →+* K := (𝒪).subtype
  let g' : (𝒪)⟦X⟧ := PowerSeries.mk fun n => ⟨coeff n g, (mem_ball _).2 (hg1 n)⟩
  let h' : (𝒪)⟦X⟧ := PowerSeries.mk fun n => ⟨coeff n h, (mem_ball _).2 (hh n)⟩
  have hg' : PowerSeries.map ι g' = g := by ext n; simp [g', ι]
  have hh' : PowerSeries.map ι h' = h := by ext n; simp [h', ι]
  obtain ⟨a, has, hamax⟩ := Finset.exists_max_image
    (insert (0 : K) ((Finset.range d).image fun n => coeff n g)) (fun x => ‖x‖)
    ⟨0, Finset.mem_insert_self _ _⟩
  have ha1 : ‖a‖ < 1 := by
    rcases Finset.mem_insert.1 has with rfl | h2
    · simp
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 h2
      exact hlt n (Finset.mem_range.1 hn)
  have hle : ∀ n < d, ‖coeff n g‖ ≤ ‖a‖ := fun n hn =>
    hamax _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hn)))
  let a' : 𝒪 := ⟨a, (mem_ball _).2 ha1.le⟩
  haveI : IsAdicComplete (Ideal.span {a'}) 𝒪 := isAdicComplete_span a' ha1
  have hgdU : IsUnit (coeff d g') := isUnit_of_norm_eq_one _ (by simpa [g'] using hgd)
  have hI : Ideal.span {a'} ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝒪) ∈ (Ideal.span {a'}) ^ 1 := by rw [pow_one, htop]; trivial
    rw [mem_span_pow] at h1
    have : ‖(a' : K)‖ = ‖a‖ := rfl
    simp only [OneMemClass.coe_one, norm_one, pow_one] at h1
    linarith
  have hord : (g'.map (Ideal.Quotient.mk (Ideal.span {a'}))).order = d := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem]
      intro hmem
      exact hI (Ideal.eq_top_of_isUnit_mem _ hmem hgdU)
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
      have h1 := (mem_span_pow a' (coeff i g') 1).2 (by simpa [g', a'] using hle i hi)
      rwa [pow_one] at h1
  have H : g'.IsWeierstrassDivisorAt (Ideal.span {a'}) := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord, ENat.toNat_coe]
    exact hgdU
  have hdiv := H.isWeierstrassDivisionAt_div_mod h'
  refine ⟨PowerSeries.map ι (H.div h'), PowerSeries.map ι (H.mod h' : (𝒪)⟦X⟧),
    fun n => ?_, fun n => ?_, fun n hn => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]; exact (mem_ball _).1 (coeff n (H.div h')).2
  · rw [PowerSeries.coeff_map]; exact (mem_ball _).1 (coeff n (H.mod h' : (𝒪)⟦X⟧)).2
  · rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt, map_zero]
    have hdl := hdiv.degree_lt
    rw [hord, ENat.toNat_coe] at hdl
    exact lt_of_lt_of_le hdl (by exact_mod_cast hn)
  · have e := congrArg (PowerSeries.map ι) hdiv.eq_mul_add
    rw [hh', map_add, map_mul, hg'] at e
    exact e

theorem first_unit_index (g : K⟦X⟧) (m : ℕ) (hg1 : ∀ n, ‖coeff n g‖ ≤ 1)
    (hm : ‖coeff m g‖ = 1) : ∃ d ≤ m, ‖coeff d g‖ = 1 ∧ ∀ n < d, ‖coeff n g‖ < 1 := by
  classical
  have hex : ∃ n, ‖coeff n g‖ = 1 := ⟨m, hm⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hm, Nat.find_spec hex,
    fun n hn => lt_of_le_of_ne (hg1 n) (Nat.find_min hex hn)⟩

end GlobalTheory.GcdGen

namespace GlobalTheory

theorem exists_primitive_generator : ∀ (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (J : Set K⟦X⟧), (∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) →
    (∀ x ∈ J, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J) →
    (∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) →
    ∃ Δ ∈ J, (∀ n, ‖coeff n Δ‖ ≤ 1) ∧ (∃ n, ‖coeff n Δ‖ = 1) ∧
      ∀ h ∈ J, (∀ n, ‖coeff n h‖ ≤ 1) → ∃ q : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ h = Δ * q := by
  intro K _ _ _ J hadd hmul ⟨g0, hg0J, hg01, m0, hm0⟩
  classical
  let S : ℕ → Prop := fun d => ∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ‖coeff d g‖ = 1 ∧
    ∀ n < d, ‖coeff n g‖ < 1
  have hS : ∃ d, S d := by
    obtain ⟨d, -, hd1, hd2⟩ := GcdGen.first_unit_index g0 m0 hg01 hm0
    exact ⟨d, g0, hg0J, hg01, hd1, hd2⟩
  obtain ⟨Δ, hΔJ, hΔ1, hΔd, hΔlt⟩ := Nat.find_spec hS
  refine ⟨Δ, hΔJ, hΔ1, ⟨_, hΔd⟩, fun h hhJ hh1 => ?_⟩
  obtain ⟨q, r, hq1, hr1, hr0, hqr⟩ := GcdGen.wdiv Δ h (Nat.find hS) hΔ1 hΔd hΔlt hh1
  have hrJ : r ∈ J := by
    have h1 : (-q) * Δ ∈ J := hmul Δ hΔJ (-q) ⟨1, fun n => by simpa using hq1 n⟩
    have h2 := hadd h hhJ _ h1
    have e : r = h + (-q) * Δ := by rw [hqr]; ring
    rw [e]; exact h2
  by_cases hr : r = 0
  · exact ⟨q, hq1, by rw [hqr, hr, add_zero, mul_comm]⟩
  exfalso
  have hex : ∃ n, coeff n r ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hr (PowerSeries.ext fun n => by simpa using hne n)
  obtain ⟨n0, hn0⟩ := hex
  have hn0d : n0 < Nat.find hS := by
    by_contra hc; exact hn0 (hr0 n0 (not_lt.1 hc))
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (Nat.find hS))
    (fun n => ‖coeff n r‖) ⟨n0, Finset.mem_range.2 hn0d⟩
  have hmd : m < Nat.find hS := Finset.mem_range.1 hm
  have hrle : ∀ n, ‖coeff n r‖ ≤ ‖coeff m r‖ := fun n => by
    by_cases hn : n < Nat.find hS
    · exact hmax n (Finset.mem_range.2 hn)
    · rw [hr0 n (not_lt.1 hn), norm_zero]; exact norm_nonneg _
  have hcpos : 0 < ‖coeff m r‖ := by
    rcases (norm_nonneg (coeff m r)).lt_or_eq with h | h
    · exact h
    · exfalso; apply hn0
      have := hrle n0
      rw [← h] at this
      exact norm_le_zero_iff.1 this
  let r' := PowerSeries.C (R := K) (coeff m r)⁻¹ * r
  have hcoeff : ∀ n, coeff n r' = (coeff m r)⁻¹ * coeff n r := fun n => by
    simp [r', PowerSeries.coeff_C_mul]
  have hr'J : r' ∈ J := hmul r hrJ _ ⟨‖(coeff m r)⁻¹‖, fun n => by
    rw [PowerSeries.coeff_C]; split_ifs <;> simp⟩
  have hr'1 : ∀ n, ‖coeff n r'‖ ≤ 1 := fun n => by
    rw [hcoeff, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]; exact hrle n
  have hr'm : ‖coeff m r'‖ = 1 := by
    rw [hcoeff, norm_mul, norm_inv]; exact inv_mul_cancel₀ hcpos.ne'
  obtain ⟨d', hd'm, hd'1, hd'lt⟩ := GcdGen.first_unit_index r' m hr'1 hr'm
  have hmin := Nat.find_min' hS ⟨r', hr'J, hr'1, hd'1, hd'lt⟩
  omega

end GlobalTheory
