import Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.InjectiveDecompositionAction

variable {D : D7}

def FirstPropositionFrame (D : D7) : Subgroup (AE D)ˣ where
  carrier := {x | (x : AE D) * cA D (x : AE D) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    calc (a : AE D) * b * (cA D a * cA D b) = (a * cA D a) * (b * cA D b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (AE D)ˣ) : AE D) * a = 1 := by simp
    have h2 : cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D) = 1 := by rw [← map_mul, h1, map_one]
    calc ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D)
        = ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D) * ((a : AE D) * cA D (a : AE D)) := by
          rw [ha, mul_one]
      _ = (((a⁻¹ : (AE D)ˣ) : AE D) * a) * (cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]

def SuppAtU (D : D7) (e : AE D) (x : (AE D)ˣ) : Prop :=
  (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1

def SvNSchur (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ T : Module.End ℂ (Hth ψ V W),
    (∀ w₀ (Φ Φ' : Hth ψ V W), (Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W w₀ Φ →
      (T Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W w₀ (T Φ)) →
    (∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL V W) 𝓕 μ → ∀ Φ : Hth ψ V W,
        ∫⁻ w in 𝓕, ‖(T Φ : WA V W → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(Φ : WA V W → ℂ) w‖ₑ ^ 2 ∂μ) →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Φ : Hth ψ V W, T Φ = c • Φ

def ThetaNZ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∃ Φ : Hth ψ V W, (Φ : WA V W → ℂ) 0 ≠ 0

def SplitFormsNZ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ e, IsSplitIdem D e → ∃ ℓ : Hth ψ V W →ₗ[ℂ] ℂ,
    (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) →
      ∀ Φ Φ' : Hth ψ V W, (Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W u Φ → ℓ Φ' = ℓ Φ) ∧
    ∃ Φ, ℓ Φ ≠ 0

def CharDet (V : HSp D) : Prop :=
  ∀ c : GA D V →* Circle, Continuous c →
    ∃ lam : FirstPropositionFrame D →* Circle, Continuous lam ∧
      ∀ (g : GA D V) (x : FirstPropositionFrame D), (((x : (AE D)ˣ)) : AE D) = (mt V g).det → c g = lam x

def SecondCharacterFact (D : D7) : Prop :=
  ∀ lam : FirstPropositionFrame D →* Circle, Continuous lam →
    (∀ (x : FirstPropositionFrame D) (q : D.host.E), (((x : (AE D)ˣ)) : AE D) = incA D q → lam x = 1) →
    (∀ e, IsSplitIdem D e → ∀ x : FirstPropositionFrame D, SuppAtU D e (x : (AE D)ˣ) → lam x = 1) →
    ∀ x, lam x = 1

def ConsequenceOfAdmissibleConstants : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W)),
    SvNSchur ψ V W → ThetaNZ ψ V W → SplitFormsNZ ψ V W → CharDet V → CharDet W → SecondCharacterFact D →
    IsWeilDatum ψ V W χ χ' ω → IsWeilDatum ψ V W χ χ' ω' → ω = ω'

end Formalism.IndefR.InjectiveDecompositionAction

end
