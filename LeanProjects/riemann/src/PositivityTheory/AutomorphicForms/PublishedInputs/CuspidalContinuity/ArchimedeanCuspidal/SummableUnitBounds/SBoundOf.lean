import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology Finset
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.LU

def zz {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ν : Fˣ →* ℂˣ) : Fin 3 → ℂˣ := ![ν (unifUnit F), 1, (ν (unifUnit F))⁻¹]

def hc (w : Fin 3 → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ Icc 0 m, ∑ z ∈ Icc 0 x, w 0 ^ z * w 1 ^ (x - z) * w 2 ^ (m - x)

def SPsi : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ x ∈ 𝒪[F], Circle.coeHom.compAddChar ψ x = 1

def SDg : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ a b c : Fˣ, ∃ k ∈ integralGL F 3,
      (dg a b c : GL (Fin 3) F) = torusPow F 3 ![ord (a : F), ord (b : F), ord (c : F)] * k

def SHalf : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ l : Fin 3 → ℤ, halfModulus F l = (residueCard F : ℂ) ^ (l 2 - l 0)

def SUni : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (x y z : F) (g : GL (Fin 3) F),
      sphW ψ ν (uni x y z * g) = (ψ (x + z) : ℂ) * sphW ψ ν g

def SGT : Prop :=
  ∀ (A B : ℕ), B ≤ A → ∀ w : Fin 3 → ℂˣ,
    evalAt w (schur ![(A : ℤ), B, 0]) =
      ∑ x ∈ Icc B A, ∑ y ∈ range (B + 1), ∑ z ∈ Icc y x,
        (w 0 : ℂ) ^ z * (w 1 : ℂ) ^ (x + y - z) * (w 2 : ℂ) ^ (A + B - x - y)

def SBound : Prop :=
  ∀ w : Fin 3 → ℂˣ, (∀ i, ‖(w i : ℂ)‖ = 1) → ∀ l : Fin 3 → ℤ, Antitone l →
    ‖evalAt w (schur l)‖ ≤ 4 ^ (l 0 - l 2).toNat

def SRows : Prop :=
  ∀ (α : ℂˣ) (m : ℕ),
    evalAt ![α, 1, α⁻¹] (schur ![(m : ℤ), 0, 0]) = hc ![(α : ℂ), 1, ((α⁻¹ : ℂˣ) : ℂ)] m ∧
    evalAt ![α, 1, α⁻¹] (schur ![0, 0, -(m : ℤ)]) = hc ![(α : ℂ), 1, ((α⁻¹ : ℂˣ) : ℂ)] m

def SGen : Prop :=
  ∀ (w : Fin 3 → ℂ) (x : ℂ), (∀ i, ‖w i‖ = 1) → ‖x‖ < 1 →
    HasSum (fun m => hc w m * x ^ m) ((1 - w 0 * x)⁻¹ * (1 - w 1 * x)⁻¹ * (1 - w 2 * x)⁻¹)

def SShell : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ g : ℤ → ℂ, Summable (fun k => ‖g k‖) →
      Integrable (fun a : Fˣ => g (ord (a : F))) (multHaar F) ∧
        ∫ a : Fˣ, g (ord (a : F)) ∂multHaar F = ∑' k, g k

def SUnr : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ c : Fˣ →* ℂˣ, IsUnramifiedChar c → ∀ a : Fˣ, c a = c (unifUnit F) ^ ord (a : F)

def SVol : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → selfDualMeasure ψ (𝒪[F] : Set F) = 1

def SCyc : Prop := SDg → SHalf → SUni →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ ν : Fˣ →* ℂˣ, ∀ (t : Fˣ) (u : F),
      (u ∈ 𝒪[F] → sphW ψ ν (mm t u) = sphW ψ ν (dg 1 1 t)) ∧ (u ∉ 𝒪[F] → sphW ψ ν (mm t u) = 0)

def SGauge : Prop := SPsi → SDg → SHalf → SBound →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν →
    ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
      ‖sphW ψ ν (dg (a * b) b 1 * k)‖ ≤ ((modulus (a : F) : ℝ) * modulus (b : F))⁻¹ ∧
      (sphW ψ ν (dg (a * b) b 1 * k) ≠ 0 → (a : F) ∈ 𝒪[F] ∧ (b : F) ∈ 𝒪[F])

def SInt1 : Prop := SPsi → SDg → SHalf → SRows → SGen → SShell → SUnr →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ ν c : Fˣ →* ℂˣ, IsUnit1 ν → IsUnit1 c →
      IsUnramifiedChar ν → IsUnramifiedChar c →
      ∀ s : ℂ, 0 < s.re → ∫ a, zF (sphW ψ ν) c s a ∂multHaar F = lf3 ν c s

def SInt2 : Prop := SPsi → SDg → SHalf → SUni → SCyc → SRows → SGen → SShell → SUnr → SVol →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F],
    ∀ ψ : AddChar F Circle, IsStd ψ → ∀ ν c : Fˣ →* ℂˣ, IsUnit1 ν → IsUnit1 c →
      IsUnramifiedChar ν → IsUnramifiedChar c →
      ∀ s : ℂ, s.re < 1 →
        ∫ p, zF' (sphW ψ ν) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) = lf3 ν c⁻¹ (1 - s)

def SBoundOf : Prop := SGT → SBound

def SRowsOf : Prop := SGT → SRows

end Ad3.LU
