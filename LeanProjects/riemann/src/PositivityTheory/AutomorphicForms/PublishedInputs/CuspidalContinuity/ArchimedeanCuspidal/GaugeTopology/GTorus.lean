import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def col3 (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) : Matrix (Fin 2) (Fin 3) F :=
  !![k 0 0, k 0 1, y 0; k 1 0, k 1 1, y 1]

def pft (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) : ℂ :=
  ∫ y, Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ) ∂vol2 ψ

def SG (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ C : ℝ, ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    ‖W (dg (a * b) b 1 * k)‖ ≤ C * ((modulus (a : F) : ℝ) * modulus (b : F)) ^ (3 / 4 : ℝ)

def Supp (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ B : ℝ, ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B ∧ (modulus (b : F) : ℝ) ≤ B

def Sm (W : GL (Fin 3) F → ℂ) : Prop := ∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, W (g * u) = W g

def om (R : ℝ) (t : Fˣ) : Set (GL (Fin 2) F) :=
  {k | (∀ i j, (modulus ((k : Matrix (Fin 2) (Fin 2) F) i j) : ℝ) ≤ R) ∧
    ∀ j, (modulus ((t : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) ≤ R}

end D

def GTorus : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ t₁ t₂ : Fˣ,
    Wp ψ W' Φ (dg t₁ t₂ 1) = mp (t₁ * t₂) (1 / 2) *
      ∫ k, W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ∂hG ψ

def GFour : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ SB F, ∃ C R : ℝ, ∀ k ξ,
    ‖pft ψ Φ k ξ‖ ≤ C ∧
      (pft ψ Φ k ξ ≠ 0 → (∀ i j, (modulus (k i j) : ℝ) ≤ R) ∧ ∀ j, (modulus (ξ j) : ℝ) ≤ R)

def GInt2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ V', WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W' ∈ V',
    ∀ R : ℝ, ∃ C : ℝ, ∀ t₁ t₂ : Fˣ,
      Integrable ((om R t₂).indicator fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ))
        (hG ψ) ∧
      ∫ k, (om R t₂).indicator (fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)) k ∂hG ψ ≤
        C * (modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ)

def GTorP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ C : ℝ, ∀ t₁ t₂ : Fˣ, ‖Wp ψ W' Φ (dg t₁ t₂ 1)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (3 / 4 : ℝ)

def GTor : Prop := GTorus → GFour → GInt2 → GTorP

def GK : Prop :=
  STrans → SSmoothW → GTorP →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → SG (Wp ψ W' Φ)

def GInt : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (W : GL (Fin 3) F → ℂ), Sm W → SG W → Supp W →
    ∀ s : ℂ, 1 / 4 < s.re → Integrable (zF W 1 s) (multHaar F)

def GInt' : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ),
    (∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g) → (∀ (a : Fˣ) g, W (dg a a a * g) = W g) →
    Sm W → SG W → Supp W →
    ∀ s : ℂ, s.re < 3 / 4 → Integrable (zF' W 1 s) ((multHaar F).prod (selfDualMeasure ψ))

end Ad3.LFS
