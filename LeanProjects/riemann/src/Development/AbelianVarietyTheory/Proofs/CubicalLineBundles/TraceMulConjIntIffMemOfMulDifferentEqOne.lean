import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

namespace GlobalTheory

open NumberField in
open scoped Matrix in
private theorem fractionalIdeal_eq_one_of_smul_submodule_eq_self {E : Type} [Field E] [NumberField E]
    {r : ℕ} {c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hc : c ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} (hL : L ≠ ⊥) (hfg : L.FG)
    (h : (↑c : Submodule (𝓞 E) E) • L = L) : c = 1 := by
  have key : ∀ d : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      (↑d : Submodule (𝓞 E) E) • L = L → d ≤ 1 := by
    intro d hd a ha
    have hint : IsIntegral (𝓞 E) a :=
      isIntegral_of_smul_mem_submodule L hL hfg a fun n hn =>
        hd ▸ Submodule.smul_mem_smul ha hn
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩
  have h1 : c ≤ 1 := key c h
  have h2 : c⁻¹ ≤ 1 := key c⁻¹ (by
    conv_rhs => rw [← _root_.GlobalTheory.fractionalIdeal_inv_smul_smul hc L]
    rw [h])
  refine le_antisymm h1 ?_
  calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = c * c⁻¹ := (mul_inv_cancel₀ hc).symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

open NumberField in
open scoped Matrix in

theorem _root_.GlobalTheory.trace_xi_mul_conj_int_iff_mem :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 0 < r → 𝔄 ≠ 0 → X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u} → ∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y) = n) ↔ x ∈ 𝔄 := by
  intro E _ _ _ r X 𝔄 hr h𝔄 hΛ x
  haveI : NeZero r := ⟨hr.ne'⟩
  have hξ : X.ξ0 ≠ 0 := X.ξ0_ne
  have hlat : _root_.ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hself : _root_.GlobalTheory.traceFormDual X.ξ0 X.Gm X.Λ = X.Λ :=
    (_root_.GlobalTheory.perfect_iff_traceFormDual_eq hξ X.Gm_det hlat).1 ⟨X.EF_int, X.EF_perf⟩
  have hL : _root_.GlobalTheory.hermDual X.Gm X.L' = X.L' :=
    _root_.GlobalTheory.hermDual_eq_self_iff.2 ⟨X.L'_int, X.L'_dual⟩
  have hΛ' : X.Λ = (↑𝔄 : Submodule (𝓞 E) E) • X.L' := by
    rw [hΛ]
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro v ⟨a, ha, u, hu, rfl⟩
      exact Submodule.smul_mem_smul ha hu
    · exact Submodule.smul_le.2 fun a ha u hu => Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
  have hLne : X.L' ≠ ⊥ := by
    intro hbot
    have hspan := X.Λ_span
    rw [hΛ', hbot, Submodule.smul_bot, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    exact bot_ne_top hspan
  set 𝔇 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      ↑(differentIdeal ℤ (𝓞 E)) with h𝔇
  have hconj0 : _root_.GlobalTheory.conjFrac 𝔄 ≠ 0 := _root_.GlobalTheory.conjFrac_ne_zero h𝔄
  have hsp0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ
  have hd0 := _root_.GlobalTheory.coe_different_ne_zero (E := E)
  have h𝔇0 : 𝔇 ≠ 0 := mul_ne_zero hsp0 hd0
  have heq : (↑𝔄 : Submodule (𝓞 E) E) • X.L' =
      (↑(𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹) : Submodule (𝓞 E) E) • X.L' := by
    rw [← hΛ', ← hself, _root_.GlobalTheory.traceFormDual_eq hξ, hΛ',
      _root_.GlobalTheory.hermDual_smul h𝔄, hL, _root_.GlobalTheory.fractionalIdeal_mul_smul]
  have h𝔅 : 𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹ = 𝔄 := by
    have hc := fractionalIdeal_eq_one_of_smul_submodule_eq_self
      (c := 𝔄⁻¹ * (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹))
      (mul_ne_zero (inv_ne_zero h𝔄) (mul_ne_zero (inv_ne_zero h𝔇0) (inv_ne_zero hconj0)))
      hLne X.L'_fg (by
        rw [_root_.GlobalTheory.fractionalIdeal_mul_smul, ← heq,
          _root_.GlobalTheory.fractionalIdeal_inv_smul_smul h𝔄])
    calc _ = 𝔄 * (𝔄⁻¹ * (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹)) := by
          rw [← mul_assoc, mul_inv_cancel₀ h𝔄, one_mul]
      _ = 𝔄 := by rw [hc, mul_one]
  have hmain : 𝔄 * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      _root_.GlobalTheory.conjFrac 𝔄) = (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
    rw [show 𝔄 * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
        _root_.GlobalTheory.conjFrac 𝔄) = (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹) *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
        _root_.GlobalTheory.conjFrac 𝔄) by rw [h𝔅], h𝔇, mul_inv]
    calc _ = (↑(differentIdeal ℤ (𝓞 E)))⁻¹ *
          ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0)⁻¹ *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0) *
          ((_root_.GlobalTheory.conjFrac 𝔄)⁻¹ * _root_.GlobalTheory.conjFrac 𝔄) := by
          first | ring | simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = _ := by rw [inv_mul_cancel₀ hsp0, inv_mul_cancel₀ hconj0, mul_one, mul_one]
  have hcc : ∀ w : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc w) = w := by
    intro w
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp
  constructor
  · intro hx
    set K := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      _root_.GlobalTheory.conjFrac 𝔄 with hK
    have hK0 : K ≠ 0 := mul_ne_zero hsp0 hconj0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * K ≤
        (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
      rw [hK, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [_root_.GlobalTheory.mem_inv_different_iff]
      intro a ha
      have h1 : (z : E) * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        _root_.GlobalTheory.mem_one_fractionalIdeal_iff.2 ((RingOfIntegers.isIntegral_coe z).mul ha)
      have hw : (z : E) * a * j ∈ _root_.GlobalTheory.conjFrac 𝔄 := by
        have := FractionalIdeal.mul_mem_mul h1 hj
        rwa [one_mul] at this
      obtain ⟨n, hn⟩ := hx (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((z : E) * a * j)) (_root_.GlobalTheory.mem_conjFrac.1 hw)
      refine ⟨n, ?_⟩
      rw [← hn, hcc]
      congr 1
      change (z : E) * (x * X.ξ0) * j * a = _
      ring
    have hsub : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x ≤ 𝔄 := by
      calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x
          = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * K * K⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hK0, mul_one]
        _ ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ * K⁻¹ := by gcongr
        _ = 𝔄 := by rw [← hmain, mul_assoc, mul_inv_cancel₀ hK0, mul_one]
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 hsub
  · intro hx y hy
    have hmem : X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y ∈ (↑(differentIdeal ℤ (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ := by
      rw [← hmain]
      have := FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mul_mem_mul
        (FractionalIdeal.mem_spanSingleton_self _ X.ξ0)
        (_root_.GlobalTheory.cc_mem_conjFrac.2 hy))
      convert this using 1
      ring
    obtain ⟨k, hk⟩ := (_root_.GlobalTheory.mem_inv_different_iff.1 hmem) 1 isIntegral_one
    exact ⟨k, by simpa using hk⟩

end GlobalTheory
