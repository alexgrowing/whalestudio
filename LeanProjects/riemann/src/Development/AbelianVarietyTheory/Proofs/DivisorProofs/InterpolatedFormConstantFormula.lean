import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory

theorem curvature_term_algebra : ∀ {n : Type} [Fintype n] {P₀ P : Matrix n n ℂ} (σ : ℝ) {θ₀ θ θs : Matrix n n ℂ} {d ℓ Φ₀ Φ Φs D₀ D Ds : ℂ} {v : n → ℂ}, P₀.IsHermitian → P.IsHermitian → Φ₀ = form P₀ (θ₀ *ᵥ v) (θ₀ *ᵥ v) - D₀ → Φ = form P (θ *ᵥ v) (θ *ᵥ v) - D → Φs = form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) (θs *ᵥ v) (θs *ᵥ v) - Ds → Ds = ((1 - σ : ℝ) : ℂ) * D₀ + (σ : ℂ) * D + (form P v v - form P₀ v v) * ℓ + d * (form P v (θ *ᵥ v) - form P₀ v (θ₀ *ᵥ v)) + starRingEnd ℂ d * (form P (θ *ᵥ v) v - form P₀ (θ₀ *ᵥ v) v) → (∀ w, form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) ((θs - θ₀) *ᵥ v) w = (σ : ℂ) * form P ((θ - θ₀) *ᵥ v) w + d * (form P v w - form P₀ v w)) → Φs = ((1 - σ : ℝ) : ℂ) * Φ₀ + (σ : ℂ) * Φ + ((form P₀ v v - form P v v) * ℓ - 2 * ((d * starRingEnd ℂ (form P ((θ - θ₀) *ᵥ v) v)).re : ℂ) + form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) ((θs - θ₀) *ᵥ v) ((θs - θ₀) *ᵥ v) - (σ : ℂ) * form P ((θ - θ₀) *ᵥ v) ((θ - θ₀) *ᵥ v)) := by
  intro n _ P₀ P σ θ₀ θ θs d ℓ Φ₀ Φ Φs D₀ D Ds v hP₀ hP hΦ₀ hΦ hΦs hDs hX
  subst hΦ₀ hΦ hΦs hDs
  have eθs : θs *ᵥ v = θ₀ *ᵥ v + (θs - θ₀) *ᵥ v := by rw [sub_mulVec]; abel
  have eθ : θ *ᵥ v = θ₀ *ᵥ v + (θ - θ₀) *ᵥ v := by rw [sub_mulVec]; abel
  have h1 := hX (θ₀ *ᵥ v)
  have h2 : form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) (θ₀ *ᵥ v) ((θs - θ₀) *ᵥ v) =
      starRingEnd ℂ (form (((1 - σ : ℝ) : ℂ) • P₀ + (σ : ℂ) • P) ((θs - θ₀) *ᵥ v) (θ₀ *ᵥ v)) := by
    simp only [form_add, form_smul, map_add, map_mul, Complex.conj_ofReal, conj_form hP₀, conj_form hP]
  rw [eθs, eθ]
  generalize θ₀ *ᵥ v = a at *
  generalize (θs - θ₀) *ᵥ v = X at *
  generalize (θ - θ₀) *ᵥ v = Y at *
  simp only [form_add_left, form_add_right]
  have h3 : ∀ z : ℂ, (2 : ℂ) * (z.re : ℂ) = z + starRingEnd ℂ z := fun z => by
    rw [Complex.add_conj]; push_cast; ring
  rw [h2, h1, h3]
  simp only [form_add, form_smul, map_add, map_sub, map_mul, Complex.conj_ofReal, conj_form hP₀,
    conj_form hP, Complex.conj_conj, form_sub_right]
  ring

end GlobalTheory
