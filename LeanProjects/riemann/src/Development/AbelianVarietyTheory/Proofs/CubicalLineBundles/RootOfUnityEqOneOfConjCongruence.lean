import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem isIntegral_eigenvalue_sub_one_div {E : Type} [Field E] [NumberField E] {r M : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ)
    (hM : (M : ℂ) ≠ 0) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hγ : ∀ x ∈ Λ, ∃ y ∈ Λ, γ *ᵥ x - x = (M : E) • y)
    (w : Fin r → ℂ) (hw : w ≠ 0) (l : ℂ) (hl : w ᵥ* γ.map τ = l • w) :
    IsIntegral ℤ ((l - 1) / M) := by
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun x => w ⬝ᵥ (τ ∘ x)
      map_zero' := by simp [dotProduct]
      map_add' := fun x y => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ x, φ x = w ⬝ᵥ (τ ∘ x) := fun _ => rfl
  have hsm : ∀ (c : E) x, φ (c • x) = τ c * φ x := by
    intro c x
    simp only [hφ, dotProduct, Finset.mul_sum, Function.comp, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmul : ∀ x, φ (γ *ᵥ x) = l * φ x := by
    intro x
    have : τ ∘ (γ *ᵥ x) = γ.map τ *ᵥ (τ ∘ x) := funext fun i => RingHom.map_mulVec τ γ x i
    rw [hφ, this, Matrix.dotProduct_mulVec, hl, smul_dotProduct, hφ, smul_eq_mul]
  refine isIntegral_of_smul_mem_submodule
    ((Λ.restrictScalars ℤ).map φ.toIntLinearMap) ?_ (hfg.restrictScalars.map _) _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := by
      intro x hx
      have : φ.toIntLinearMap x ∈ (Λ.restrictScalars ℤ).map φ.toIntLinearMap :=
        Submodule.mem_map_of_mem hx
      rw [h0] at this
      simpa using this
    have h2 : ∀ x ∈ Submodule.span E (Λ : Set (Fin r → E)), φ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [hsm, hx, mul_zero]
    apply hw
    funext i
    have h3 := h2 (Pi.single i 1) (hsp ▸ Submodule.mem_top)
    have h4 : τ ∘ (Pi.single i 1 : Fin r → E) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hφ, h4] at h3
    simpa using h3
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hγ x hx
    refine ⟨y, hy, ?_⟩
    have h := congrArg φ hxy
    rw [map_sub, hmul, hsm, map_natCast] at h
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
    field_simp
    linear_combination -h

theorem root_of_unity_eq_one_of_isIntegral_div {E : Type} [Field E] [NumberField E] {M n : ℕ}
    (hM : 3 ≤ M) (hn : 0 < n) {u : E} (hu : u ^ n = 1) (h : IsIntegral ℤ ((u - 1) / M)) :
    u = 1 := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hlt : ∀ φ : E →+* ℂ, ‖φ ((u - 1) / M)‖ < 1 := by
    intro φ
    have h1 : ‖φ u‖ = 1 := by
      have : ‖φ u‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h2 : ‖φ u - 1‖ ≤ 2 := by
      have := norm_sub_le (φ u) 1
      rw [h1, norm_one] at this
      linarith
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    linarith
  by_contra hne
  have hx : (u - 1) / M ≠ 0 := div_ne_zero (sub_ne_zero.2 hne) hM0
  obtain ⟨k, hk, hk1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx h
    fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : ‖φ ((u - 1) / M)‖ ^ k = 1 := by rw [← norm_pow, ← map_pow, hk1, map_one, norm_one]
  exact (hlt φ).ne ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3)

theorem root_of_unity_eq_one_of_conj_congruence :
    ∀ (E : Type) [Field E] [NumberField E] (r M n : ℕ) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (γ δ : Matrix (Fin r) (Fin r) E) (u : E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), 0 < r → 3 ≤ M → 0 < n → u ^ n = 1 → Λ.FG → Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → (∀ x ∈ Λ', ∃ y ∈ Λ', Matrix.mulVec (δ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → Q.det ≠ 0 → (u • γ).map τ * Q = Q * δ.map τ → u = 1 := by
  intro E _ _ r M n Λ Λ' γ δ u τ Q hr hM hn hu hfg hfg' hsp hsp' hγ hδ hQ hconj
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (γ.map τ)ᵀ)
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hw1 : w ᵥ* γ.map τ = l • w := by
    have := hw.apply_eq_smul
    rwa [Matrix.toLin'_apply, Matrix.mulVec_transpose] at this
  have hwQ : w ᵥ* Q ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_vecMul_eq_zero hQ h)
  have hs : (u • γ).map τ = τ u • γ.map τ := by
    ext i j; simp
  have hw2 : (w ᵥ* Q) ᵥ* δ.map τ = (τ u * l) • (w ᵥ* Q) := by
    rw [Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul, hs, Matrix.vecMul_smul, hw1,
      smul_smul, Matrix.smul_vecMul]
  have ha := isIntegral_eigenvalue_sub_one_div Λ γ τ hM0 hfg hsp hγ w hw0 l hw1
  have hb := isIntegral_eigenvalue_sub_one_div Λ' δ τ hM0 hfg' hsp' hδ _ hwQ _ hw2
  have hui : IsIntegral ℤ (τ u) := by
    apply IsIntegral.of_pow hn
    rw [← map_pow, hu, map_one]
    exact isIntegral_one
  have hc : τ ((u - 1) / M) = (τ u * l - 1) / M - τ u * ((l - 1) / M) := by
    rw [map_div₀, map_sub, map_one, map_natCast]
    field_simp
    ring
  refine root_of_unity_eq_one_of_isIntegral_div hM hn hu ?_
  refine (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 ?_
  change IsIntegral ℤ (τ ((u - 1) / M))
  rw [hc]
  exact hb.sub (hui.mul ha)

end GlobalTheory
