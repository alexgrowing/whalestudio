import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.SchwartzSpaceL2

def pt {F : Type} (f g : F → ℂ) : (Fin 2 → F) → ℂ := fun x => f (x 0) * g (x 1)

def rt {F : Type} [Field F] (φ : (Fin 2 → F) → ℂ) (h : GL (Fin 2) F) : (Fin 2 → F) → ℂ :=
  fun x => φ (x ᵥ* (h : Matrix (Fin 2) (Fin 2) F))

def SPsi : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ (x : F) (g : GL (Fin 2) F),
      W2 ψ μ₁ μ₂ φ (uni2 x * g) = (ψ x : ℂ) * W2 ψ μ₁ μ₂ φ g

def SCen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ (a : Fˣ) (g : GL (Fin 2) F),
      W2 ψ μ₁ μ₂ φ (dg2 a a * g) = ((μ₁ a * μ₂ a : ℂˣ) : ℂ) * W2 ψ μ₁ μ₂ φ g

def STrans : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ h : GL (Fin 2) F,
      rt φ h ∈ GodementSectionLocal.schwartzBruhat2 F ∧ ∀ g : GL (Fin 2) F,
        W2 ψ μ₁ μ₂ φ (g * h) = ((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2) *
          W2 ψ μ₁ μ₂ (rt φ h) g

def SSmooth : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∃ U : OpenSubgroup (GL (Fin 2) F),
      ∀ g, ∀ u ∈ U, W2 ψ μ₁ μ₂ φ (g * u) = W2 ψ μ₁ μ₂ φ g

def SBound : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, ∀ (a : Fˣ),
      ∀ k ∈ GLnLocal.integralGL F 2,
        ‖W2 ψ μ₁ μ₂ φ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
          (W2 ψ μ₁ μ₂ φ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)

def SNe : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∃ φ ∈ GodementSectionLocal.schwartzBruhat2 F, W2 ψ μ₁ μ₂ φ 1 ≠ 0

def SUnr : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    IsUnramifiedChar μ₁ → IsUnramifiedChar μ₂ →
      W2 ψ μ₁ μ₂ (Set.indicator {x | ∀ i, x i ∈ 𝒪[F]} 1) =
        Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![μ₁ (unifUnit F), μ₂ (unifUnit F)]

def SDZ : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F],
    ∀ f ∈ schwartzBruhat F, ∀ G ∈ schwartzBruhat F, ∀ α β : Fˣ →* ℂˣ, IsUnit1 α → IsUnit1 β →
      ∀ s : ℂ, 0 < s.re →
        Integrable (fun a : Fˣ => ((α a : ℂˣ) : ℂ) * mp a s *
          ∫ h : Fˣ, ((β h : ℂˣ) : ℂ) * f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F) ∂multHaar F) (multHaar F) ∧
        ∫ a : Fˣ, ((α a : ℂˣ) : ℂ) * mp a s *
            (∫ h : Fˣ, ((β h : ℂˣ) : ℂ) * f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F) ∂multHaar F) ∂multHaar F =
          localZeta f α s * localZeta G (α * β⁻¹) s

def SWd : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ f ∈ schwartzBruhat F, ∀ g ∈ schwartzBruhat F, ∀ a : Fˣ,
      W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) = ((μ₂ a : ℂˣ) : ℂ) * mp a (1 / 2) *
        ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * f ((h : F) * a) *
          localFourier (selfDualMeasure ψ) ψ g (-((h⁻¹ : Fˣ) : F)) ∂multHaar F

def SPure : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F],
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∃ (n : ℕ) (f g : Fin n → F → ℂ),
      (∀ i, f i ∈ schwartzBruhat F ∧ g i ∈ schwartzBruhat F) ∧ φ = ∑ i, pt (f i) (g i)

def SLin : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ₁ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ φ₂ ∈ GodementSectionLocal.schwartzBruhat2 F,
      W2 ψ μ₁ μ₂ (φ₁ + φ₂) = W2 ψ μ₁ μ₂ φ₁ + W2 ψ μ₁ μ₂ φ₂ ∧ ∀ c : ℂ, W2 ψ μ₁ μ₂ (c • φ₁) = c • W2 ψ μ₁ μ₂ φ₁

def STate : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ χ : Fˣ →* ℂˣ, IsUnit1 χ → ∀ f ∈ schwartzBruhat F, ∀ s : ℂ,
      0 < s.re → s.re < 1 →
        localZeta (localFourier (selfDualMeasure ψ) ψ f) χ⁻¹ (1 - s) = gam ψ χ s * localZeta f χ s ∧
        localZeta f χ⁻¹ (1 - s) =
          ((χ (-1) : ℂˣ) : ℂ) * gam ψ χ s * localZeta (localFourier (selfDualMeasure ψ) ψ f) χ s

def FeGen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ →
    ∀ φ ∈ GodementSectionLocal.schwartzBruhat2 F, ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 →
      Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ φ (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) (multHaar F) ∧
      Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ φ (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ φ (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
        gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
          ∫ a, W2 ψ μ₁ μ₂ φ (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

def SFe : Prop := SDZ → SWd → SPure → SLin → STrans → STate → FeGen

end Ad3.SchwartzSpaceL2
