import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem exists_pos_nat_mem_fractionalIdeal {E : Type} [Field E] [NumberField E]
    {a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ a := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger ha
  have hI : (Ideal.span {x} : Ideal (𝓞 E)) ≠ ⊥ := by simpa using hx0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨Ideal.absNorm (Ideal.span {x}),
    Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
  have h := (a : Submodule (𝓞 E) E).smul_mem e hx
  rw [Algebra.smul_def, ← map_mul, he, map_natCast] at h
  exact h

theorem fractionalIdeal_smul_eq_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by
  refine le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, u, hu, rfl⟩
  exact Submodule.smul_mem_smul hα hu

theorem exists_dataX_of_perfect_traceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔄 𝔄b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (k : ℝ) (g : ℕ), (∀ a : E, a ∈ 𝔄b ↔ cc a ∈ 𝔄) → FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * 𝔄 * 𝔄b * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = k) → k ≤ 1 → (∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ n : ℤ, EFf X.ξ0 X.Gm x y = n) → (∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y) → 0 < g → (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ) → ∃ Xx : DataX E r, Xx.toData = X ∧ Xx.g = g ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro E _ _ _ r X 𝔄 𝔄b k g hb hone habs hk hint hperf hg hcong
  have hbc : 𝔄b = conjFrac 𝔄 := by
    ext a; rw [mem_conjFrac]; exact hb a
  subst hbc
  have hA : 𝔄 ≠ 0 := by
    rintro rfl
    simp at hone
  have hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hd := (perfect_iff_hermDual_eq X.ξ0_ne X.Gm_det hΛ).1 ⟨hint, hperf⟩
  have hself : hermDual X.Gm (((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) • X.Λ) =
      ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ := by
    rw [hermDual_smul (inv_ne_zero hA), conjFrac_inv, inv_inv, hd, ← fractionalIdeal_mul_smul]
    congr 2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hone]; ring
  obtain ⟨hi, hdual⟩ := hermDual_eq_self_iff.1 hself
  obtain ⟨NA, hNA, hNA'⟩ := exists_pos_nat_mem_fractionalIdeal (inv_ne_zero hA)
  obtain ⟨NC, hNC, hNC'⟩ := exists_pos_nat_mem_fractionalIdeal hA
  have hk0 : 0 < k := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← habs τ, norm_pos_iff]
    exact (map_ne_zero τ).2 X.ξ0_ne
  refine ⟨{ toData := X
            k0 := 2 * k
            minWeight_pos := by positivity
            k0_le := by linarith
            ξ0_abs := fun τ => by rw [habs]; ring
            EF_int := hint
            EF_perf := hperf
            L' := ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ
            L'_fg := (isLattice_fractionalIdeal_smul (inv_ne_zero hA) hΛ).1
            L'_int := hi
            L'_dual := hdual
            NA := NA
            NC := NC
            NA_pos := hNA
            NC_pos := hNC
            NA_sub := fun x hx => Submodule.smul_mem_smul hNA' hx
            NC_sub := fun x hx => ?_
            g := g
            g_pos := hg
            cong := hcong }, rfl, rfl, ?_⟩
  · have h := Submodule.smul_mem_smul (show (NC : E) ∈ (𝔄 : Submodule (𝓞 E) E) from hNC') hx
    rwa [fractionalIdeal_smul_inv_smul hA] at h
  · change X.Λ = _
    rw [← fractionalIdeal_smul_eq_span, fractionalIdeal_smul_inv_smul hA]

end GlobalTheory
