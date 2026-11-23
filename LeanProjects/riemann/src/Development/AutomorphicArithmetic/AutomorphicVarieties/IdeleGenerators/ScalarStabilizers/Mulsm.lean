import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

theorem UpperTheory.V.Sd.Hm.mulsm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ ψ : TR.Sm F a),
        φ.1 * ψ.1 ∈ TR.Sm F a ∧ ∀ (χ : TR.Sm F a), χ.1 = φ.1 * ψ.1 → ∀ X : TR.Lie F a,
          (TR.lie F a X χ).1 = (TR.lie F a X φ).1 * ψ.1 + φ.1 * (TR.lie F a X ψ).1 := by
  intro F _ _ _ a φ ψ
  have e : ∀ g, TR.chart (φ.1 * ψ.1) g = TR.chart φ.1 g * TR.chart ψ.1 g := by
    intro g
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [TR.chart, h]
  have v : ∀ (f : GA F a → ℂ) g, TR.chart f g (TR.oneL F a) = f g := by
    intro f g
    have h := TR.chart_val f g 1
    rw [map_one, mul_one] at h
    exact h
  refine ⟨fun g => ?_, fun χ hχ X => ?_⟩
  · rw [e]
    exact (φ.2 g).mul (ψ.2 g)
  · funext g
    change TR.lieD X χ.1 g = TR.lieD X φ.1 g * ψ.1 g + φ.1 g * TR.lieD X ψ.1 g
    unfold TR.lieD
    rw [hχ, e, fderiv_mul (TR.differentiableAt_chart φ.2 g) (TR.differentiableAt_chart ψ.2 g), v, v]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
