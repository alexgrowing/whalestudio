import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

def Φ0 : Matrix (Fin 2) (Fin 3) F → ℂ := Set.indicator {X | ∀ i j, X i j ∈ 𝒪[F]} 1

def s2 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 2) F → ℂ :=
  sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![ν (unifUnit F), ν⁻¹ (unifUnit F)]

def W0 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 3) F → ℂ := Wp ψ (s2 ψ ν) (Φ0 F)

end D

def UPhi : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F], Φ0 F ∈ SB F

def UK : Prop := STrans → UPhi →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ), ∀ g, ∀ k ∈ integralGL F 3, W0 ψ ν (g * k) = W0 ψ ν g

def UUni : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ u ∈ unipotent F 3,
      u = uni ((u : Matrix (Fin 3) (Fin 3) F) 0 1) ((u : Matrix (Fin 3) (Fin 3) F) 0 2)
        ((u : Matrix (Fin 3) (Fin 3) F) 1 2) ∧
      ∀ ψ₀ : AddChar F ℂ, Whittaker.psiN ψ₀ u =
        ψ₀ ((u : Matrix (Fin 3) (Fin 3) F) 0 1 + (u : Matrix (Fin 3) (Fin 3) F) 1 2)

def UNonDom : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ W : GL (Fin 3) F → ℂ,
    (∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g) →
    (∀ g, ∀ k ∈ integralGL F 3, W (g * k) = W g) →
    ∀ l : Fin 3 → ℤ, ¬ Antitone l → W (torusPow F 3 l) = 0

def UDomA : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν →
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ l : Fin 3 → ℤ, Antitone l →
      W0 ψ ν (torusPow F 3 l) = c₀ * halfModulus F l *
        ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1),
          evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])

def UBranch : Prop :=
  ∀ (α : ℂˣ) (l : Fin 3 → ℤ), Antitone l →
    evalAt ![α, 1, α⁻¹] (schur l) =
      ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1), evalAt ![α, α⁻¹] (schur ![a, b])

def UGlue : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ ψ₀ : AddChar F ℂ, (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (W : GL (Fin 3) F → ℂ) (c : ℂ),
    (∀ u ∈ unipotent F 3, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g) →
    (∀ g, ∀ k ∈ integralGL F 3, W (g * k) = W g) →
    (∀ l, W (torusPow F 3 l) = c * sphericalWhittaker ψ₀ z (torusPow F 3 l)) →
    W = c • sphericalWhittaker ψ₀ z

end Ad3.LFS
