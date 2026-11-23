import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

instance mGL2 : MeasurableSpace (GL (Fin 2) F) := borel _
instance bGL2 : BorelSpace (GL (Fin 2) F) := ⟨rfl⟩

variable (F) in

def SB : Set (Matrix (Fin 2) (Fin 3) F → ℂ) := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}

def blk (x : Fin 2 → F) : Matrix (Fin 2) (Fin 3) F := !![1, 0, x 0; 0, 1, x 1]

def vol2 (ψ : AddChar F Circle) : Measure (Fin 2 → F) := Measure.pi fun _ => selfDualMeasure ψ

def hG (ψ : AddChar F Circle) : Measure (GL (Fin 2) F) :=
  Measures.haarGL F 2 (Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ)

def inn (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 2) F) (g : GL (Fin 3) F) : ℂ :=
  ∫ x, Φ ((h : Matrix (Fin 2) (Fin 2) F) * blk x * (g : Matrix (Fin 3) (Fin 3) F)) * (ψ (-x 1) : ℂ) ∂vol2 ψ

def Wp (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (g : GL (Fin 3) F) : ℂ :=
  mp (GeneralLinearGroup.det g) 1 *
    ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h g ∂hG ψ

def VF (ψ : AddChar F Circle) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)) : Submodule ℂ (GL (Fin 3) F → ℂ) :=
  Submodule.span ℂ {W | ∃ W' ∈ V', ∃ Φ ∈ SB F, W = Wp ψ W' Φ}

def rtr (h : GL (Fin 3) F) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) : Matrix (Fin 2) (Fin 3) F → ℂ :=
  fun X => mp (GeneralLinearGroup.det h) 1 * Φ (X * (h : Matrix (Fin 3) (Fin 3) F))

def Hyp (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) : Prop :=
  IsStd ψ ∧ IsUnit1 ν ∧ (∃ V', WhittakerModelGL2 ψ ν ν⁻¹ V' ∧ W' ∈ V') ∧ Φ ∈ SB F

structure Per (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W : GL (Fin 3) F → ℂ) : Prop where
  psi : ∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g
  cen : ∀ (a : Fˣ) g, W (dg a a a * g) = W g
  smooth : ∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, W (g * u) = W g
  gauge : ∃ (C B : ℝ) (T : ℕ), ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((modulus (a : F) : ℝ) * modulus (b : F)) ^ T ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B ∧ (modulus (b : F) : ℝ) ≤ B)
  int : ∀ s : ℂ, 1 / 4 < s.re → Integrable (zF W 1 s) (multHaar F)
  int' : ∀ s : ℂ, s.re < 3 / 4 → Integrable (zF' W 1 s) ((multHaar F).prod (selfDualMeasure ψ))
  fe : ∀ c, IsUnit1 c → ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
    ∫ p, zF' W c s p ∂((multHaar F).prod (selfDualMeasure ψ)) = gam3 ψ ν c s * ∫ a, zF W c s a ∂multHaar F

end D

def SInv : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ν : Fˣ →* ℂˣ), IsUnit1 ν → IsUnit1 ν⁻¹ ∧ (IsUnramifiedChar ν → IsUnramifiedChar ν⁻¹)

def SInd2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F], Set.indicator {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} 1 ∈ GodementSectionLocal.schwartzBruhat2 F

def SSpan : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (S : Set (GL (Fin 3) F → ℂ)),
    (∃ W ∈ S, W ≠ 0) → (∀ W ∈ S, ∀ h, (fun g => W (g * h)) ∈ S) → (∀ W ∈ S, Per ψ ν W) →
    WhF ψ ν (Submodule.span ℂ S)

def STrans : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (h : GL (Fin 3) F),
    Φ ∈ SB F → rtr h Φ ∈ SB F ∧ (fun g => Wp ψ W' Φ (g * h)) = Wp ψ W' (rtr h Φ)

def SNe : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ V', WhittakerModelGL2 ψ ν ν⁻¹ V' →
    ∃ W' ∈ V', ∃ Φ ∈ SB F, Wp ψ W' Φ ≠ 0

def SPsiW : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∀ x y z g, Wp ψ W' Φ (uni x y z * g) = (ψ (x + z) : ℂ) * Wp ψ W' Φ g

def SCenW : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∀ (a : Fˣ) g, Wp ψ W' Φ (dg a a a * g) = Wp ψ W' Φ g

def SSmoothW : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, Wp ψ W' Φ (g * u) = Wp ψ W' Φ g

def SSupp : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ W : GL (Fin 3) F → ℂ,
    (∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g) →
    (∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, W (g * u) = W g) →
    ∃ B : ℝ, ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
      W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B ∧ (modulus (b : F) : ℝ) ≤ B

def SBndW : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ (C : ℝ) (T : ℕ), ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
      ‖Wp ψ W' Φ (dg (a * b) b 1 * k)‖ ≤ C / ((modulus (a : F) : ℝ) * modulus (b : F)) ^ T

def SIntW : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∀ s : ℂ, 1 / 4 < s.re → Integrable (zF (Wp ψ W' Φ) 1 s) (multHaar F)

def SInt'W : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∀ s : ℂ, s.re < 3 / 4 → Integrable (zF' (Wp ψ W' Φ) 1 s) ((multHaar F).prod (selfDualMeasure ψ))

def SFeW : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∀ c, IsUnit1 c → ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
      ∫ p, zF' (Wp ψ W' Φ) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) =
        gam3 ψ ν c s * ∫ a, zF (Wp ψ W' Φ) c s a ∂multHaar F

def SUnr : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν →
    ∀ V', WhittakerModelGL2 ψ ν ν⁻¹ V' →
    Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![ν (unifUnit F), ν⁻¹ (unifUnit F)] ∈ V' →
    sphW ψ ν ∈ VF ψ V'

end Ad3.LFS
