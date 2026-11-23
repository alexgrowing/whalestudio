import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def RealSt : Prop := ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (β : X →ₗ[ℝ] X →ₗ[ℝ] ℝ),
  (∀ x y, β x y = β y x) → (∀ x, (∀ y, β x y = 0) → x = 0) → ∀ S : (X × X) ≃ₗ[ℝ] (X × X),
  (∀ w w', β (S w).1 (S w').2 - β (S w').1 (S w).2 = β w.1 w'.2 - β w'.1 w.2) →
  ∃ T : SchwartzMap X ℂ ≃L[ℂ] SchwartzMap X ℂ, ∀ (w : X × X) (f g : SchwartzMap X ℂ),
    (∀ x, g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x w.2 + β w.1 w.2 / 2 : ℝ) : ℂ)) * f (x + w.1)) →
    ∀ x, T g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x (S w).2 + β (S w).1 (S w).2 / 2 : ℝ) : ℂ)) * T f (x + (S w).1)

def AdelSt : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (S : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F))),
  (∀ w w', (S w).1 ⬝ᵥ (S w').2 - (S w').1 ⬝ᵥ (S w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ ≃L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)),
    (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧ (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (S w) (e Φ)) ∧
    (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
    (∀ v w, At (evFin F v) w → ∀ φ ∈ SB (κ → Fv F v), ∀ φ₁, Acts (evFin F v) (schr ψ w) φ φ₁ →
      Acts (evFin F v) (schr ψ (S w)) (ev v φ) (ev v φ₁)) ∧
    (∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)

end PositivityTheory.Mix
