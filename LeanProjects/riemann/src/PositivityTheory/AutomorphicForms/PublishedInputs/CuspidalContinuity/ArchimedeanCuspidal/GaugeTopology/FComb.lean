import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def psm (ψ : AddChar F Circle) (x : F) : ℂ := (ψ (-x) : ℂ)

def WL (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (lam : ℂ) (f : F → ℂ)
    (g : GL (Fin 3) F) : ℂ :=
  mp (GeneralLinearGroup.det g) (1 + lam) *
    ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2 + lam) *
      ∫ x, Φ ((h : Matrix (Fin 2) (Fin 2) F) * blk x * (g : Matrix (Fin 3) (Fin 3) F)) * f (x 1) ∂vol2 ψ ∂hG ψ

def fL (ψ : AddChar F Circle) (φ : F → ℂ) (x : F) : ℂ := ∫ b, φ b * (ψ (-(b * x)) : ℂ) ∂selfDualMeasure ψ

def NZ (ψ : AddChar F Circle) (φ : F → ℂ) : Prop :=
  φ ∈ schwartzBruhat F ∧ (∀ᶠ x in 𝓝 (0 : F), φ x = 0) ∧ ∫ x, φ x ∂selfDualMeasure ψ = 0

def PU (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (lam : ℂ)
    (c : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ k, inn ψ Φ k 1 * mp (GeneralLinearGroup.det k) (3 / 2 + lam) *
    ∫ a, W' (dg2 a 1 * k⁻¹) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F ∂hG ψ

variable (F) in

def kq : ℂ := (((multHaarConst F).toReal)⁻¹ : ℝ)

end D

def F0 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) W' Φ, WL ψ W' Φ 0 (psm ψ) = Wp ψ W' Φ

def FPrim : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ c, IsUnit1 c → ∀ s lam : ℂ,
    1 / 4 < s.re → -(1 / 16) < lam.re →
      Integrable (zF (WL ψ W' Φ lam (psm ψ)) c s) (multHaar F) ∧
        ∫ a, zF (WL ψ W' Φ lam (psm ψ)) c s a ∂multHaar F = PU ψ W' Φ lam c s

def FHolP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ c, IsUnit1 c → ∀ s : ℂ,
    1 / 4 < s.re → DifferentiableOn ℂ (fun lam => PU ψ W' Φ lam c s) {lam | -(1 / 16) < lam.re}

def FDual : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ φ, NZ ψ φ → ∀ c, IsUnit1 c →
    ∀ s lam : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → 1 - s.re < lam.re → lam.re < 1 →
      ∫ p, zF' (WL ψ W' Φ lam (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) =
        kq F * ((c (-1) : ℂˣ) : ℂ) * (gam ψ (ν * c) s * gam ψ (ν⁻¹ * c) s) *
          localZeta (fL ψ φ) c⁻¹ (1 - s - lam) * PU ψ W' Φ lam c s

def FHolD : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ φ, NZ ψ φ → ∀ c, IsUnit1 c →
    ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
      DifferentiableOn ℂ (fun lam => ∫ p, zF' (WL ψ W' Φ lam (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)))
          {lam | 0 < lam.re ∧ lam.re < 1} ∧
        ContinuousWithinAt (fun lam => ∫ p, zF' (WL ψ W' Φ lam (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)))
          {lam | 0 ≤ lam.re ∧ lam.re < 1} 0

def FHolT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ φ, NZ ψ φ → ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ,
    Differentiable ℂ (fun lam => localZeta (fL ψ φ) c⁻¹ (1 - s - lam))

def FTwo : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ φ, NZ ψ φ → ∀ c, IsUnit1 c →
    ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
      ∫ p, zF' (WL ψ W' Φ 0 (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) =
        kq F * localZeta φ c s * ∫ p, zF' (Wp ψ W' Φ) c s p ∂((multHaar F).prod (selfDualMeasure ψ))

def FTate : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ φ, NZ ψ φ → ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ,
    0 < s.re → s.re < 1 →
      localZeta (fL ψ φ) c⁻¹ (1 - s) = ((c (-1) : ℂˣ) : ℂ) * gam ψ c s * localZeta φ c s

def FPhi : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ∃ φ, NZ ψ φ ∧ localZeta φ c s ≠ 0

def FComb : Prop := F0 → FPrim → FHolP → FDual → FHolD → FHolT → FTwo → FTate → FPhi → SFeW

end Ad3.LFS
