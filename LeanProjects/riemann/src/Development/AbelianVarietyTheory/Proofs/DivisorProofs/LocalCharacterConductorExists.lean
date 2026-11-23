import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

noncomputable section
namespace GlobalTheory.CondRescale

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : ‖z‖ ≤ 1 := by
  by_contra hz
  push_neg at hz
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hz
  have h1 := h n
  have h2 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖z ^ n‖ = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_pow, norm_one] at h2
  linarith

theorem exists_ball_trivial (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ0 t = 1 := by
  have hc : Continuous fun t : k => ‖ψ0 t - 1‖ := (hψ.sub continuous_const).norm
  have h0 : ‖ψ0 0 - 1‖ < 1 := by simp
  have hU : {t : k | ‖ψ0 t - 1‖ < 1} ∈ nhds (0 : k) :=
    (isOpen_lt hc continuous_const).mem_nhds h0
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hU
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hp : ∀ s : k, valuation k s < γ → ∀ n : ℕ, ‖ψ0 s ^ n - 1‖ < 1 := by
    intro s hs n
    have h1 : n • s ∈ {t : k | ‖ψ0 t - 1‖ < 1} :=
      hsub (lt_of_le_of_lt (GlobalTheory.CharDualMat.valuation_nsmul_le s n) hs)
    rw [Set.mem_setOf_eq, AddChar.map_nsmul_eq_pow] at h1
    exact h1
  have hneg : valuation k (-t) < γ := by rwa [Valuation.map_neg]
  have a1 := norm_le_one_of_pow_near _ (hp t ht)
  have a2 := norm_le_one_of_pow_near _ (hp (-t) hneg)
  have hm : ψ0 (-t) * ψ0 t = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 t‖ = 1 := by
    have := congrArg norm hm
    rw [norm_mul, norm_one] at this
    nlinarith [norm_nonneg (ψ0 t), norm_nonneg (ψ0 (-t))]
  exact GlobalTheory.IrredSB.eq_one_of_forall_pow hn (hp t ht)

theorem exists_rescale_conductor_integers [CharZero k]
    (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (hne : ψ0 ≠ 1) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (c * (x * y)) = 1) ↔ x ∈ 𝒪[k] := by
  classical
  let P : k → Prop := fun a => ∀ y ∈ 𝒪[k], ψ0 (a * y) = 1
  obtain ⟨t, ht⟩ : ∃ t : k, ψ0 t ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hne (AddChar.ext _ _ fun s => by simpa using hall s)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one _)
  have hbd : ∀ a, P a → a ≠ 0 → valuation k a < valuation k t := by
    intro a ha ha0
    by_contra hle
    push_neg at hle
    apply ht
    have hmem : t / a ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    have := ha _ hmem
    rwa [mul_div_cancel₀ _ ha0] at this
  obtain ⟨γ, hγ, hball⟩ := exists_ball_trivial ψ0 hψ
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  have hPr : P (r ^ m) := by
    intro y hy
    apply hball
    rw [map_mul, map_pow]
    calc valuation k r ^ m * valuation k y ≤ valuation k r ^ m * 1 :=
          mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 hy)
      _ < γ := by simpa using hm
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hex : ∀ a : k, a ≠ 0 → ∃ n : ℤ, e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro a ha
    have h1 : e (valuation k a) ≠ 0 := by
      intro h
      apply ha
      have : valuation k a = 0 := by
        have h2 : e (valuation k a) = e 0 := by rw [h, map_zero]
        exact e.injective h2
      simpa using this
    obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h1
    exact ⟨Multiplicative.toAdd u, by simpa using hu.symm⟩
  let Q : ℤ → Prop := fun n => ∃ a, P a ∧ a ≠ 0 ∧
    e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨N, hN⟩ := hex t ht0
  have hr0' : r ^ m ≠ 0 := pow_ne_zero _ hr0
  obtain ⟨n1, hn1⟩ := hex _ hr0'
  obtain ⟨n0, ⟨a0, ha0P, ha0, hn0⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := Q)
    ⟨N, fun n ⟨a, ha, ha0, hn⟩ => by
      have h1 : e (valuation k a) < e (valuation k t) := e.strictMono (hbd a ha ha0)
      rw [hn, hN, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt] at h1
      exact h1.le⟩ ⟨n1, r ^ m, hPr, hr0', hn1⟩
  have hdown : ∀ b, P b → b ≠ 0 → valuation k b ≤ valuation k a0 := by
    intro b hb hb0
    obtain ⟨n, hn⟩ := hex b hb0
    have h1 := hmax n ⟨b, hb, hb0, hn⟩
    have h2 : e (valuation k b) ≤ e (valuation k a0) := by
      rw [hn, hn0, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
      exact h1
    exact (map_le_map_iff e).1 h2
  have hv0 : valuation k a0 ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  refine ⟨a0, ha0, fun x => ⟨fun hx => ?_, fun hx y hy => ha0P _ (mul_mem hx hy)⟩⟩
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem _
  have hP : P (a0 * x) := fun y hy => by
    rw [mul_assoc]
    exact hx y hy
  have h1 := hdown _ hP (mul_ne_zero ha0 hx0)
  rw [Valuation.mem_integer_iff]
  have h2 : valuation k x = valuation k (a0 * x) / valuation k a0 := by
    rw [map_mul, mul_div_cancel_left₀ _ hv0]
  rw [h2]
  exact (div_le_one₀ (zero_lt_iff.2 hv0)).2 h1

end GlobalTheory.CondRescale
