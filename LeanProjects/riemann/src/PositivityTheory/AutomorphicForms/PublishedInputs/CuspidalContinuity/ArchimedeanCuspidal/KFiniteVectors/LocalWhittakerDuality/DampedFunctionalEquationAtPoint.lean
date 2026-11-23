import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in

def onU (f : Fˣ → ℂ) (t : F) : ℂ := if h : t = 0 then 0 else f (Units.mk0 t h)

def what₂ (r₁ r₂ : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := Matrix.of ![r₁, r₂]

def SB2 (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) : Prop := IsLocallyConstant Φ ∧ HasCompactSupport Φ

def zA (ψ : AddChar F Circle) (W : GL (Fin 2) F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ y, onU (fun a => W (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 3 / 2)) y ∂selfDualMeasure ψ
def zA' (ψ : AddChar F Circle) (W : GL (Fin 2) F → ℂ) (ω μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ y, onU (fun a => W (dg2 a 1 * w0) * (((ω a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (-1 / 2 - s)) y ∂selfDualMeasure ψ

open Classical in

def hr (r : Fin 2 → F) : GL (Fin 2) F :=
  if hv : (!![(r 1)⁻¹, 0; r 0, r 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv else 1

def phk (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (t : F) (r₂ : Fin 2 → F) : ℂ :=
  ∫ r₁, Φ (what₂ r₁ r₂) * ((ψ⁻¹ (r₁ 1 / r₂ 1 - t * (r₁ 0 * r₂ 1 - r₁ 1 * r₂ 0)) : Circle) : ℂ) ∂LFS.vol2 ψ

def phd (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (g : GL (Fin 2) F) : ℂ :=
  ∫ r, Φ (what₂ r (fun j => g.val 0 j / (g.val).det)) * ((ψ⁻¹ (r 0 * g.val 1 1 - r 1 * g.val 1 0) : Circle) : ℂ) ∂LFS.vol2 ψ

def gjI (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (W : GL (Fin 2) F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (g : GL (Fin 2) F) : ℂ :=
  Φ g.val * W g * ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s + 1 / 2)
def gjdI (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (W : GL (Fin 2) F → ℂ) (ω μ : Fˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 2) F) : ℂ :=
  phd ψ Φ g * W g * ((((ω * μ) (GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (1 / 2 - s)

def GJ (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (W : GL (Fin 2) F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ g, gjI Φ W μ s g ∂LFS.hG ψ
def GJd (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (W : GL (Fin 2) F → ℂ) (ω μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ g, gjdI ψ Φ W ω μ s g ∂LFS.hG ψ

def itI (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (J : (GL (Fin 2) F → ℂ) → ℂ) (W : GL (Fin 2) F → ℂ) : ℂ :=
  ∫ r₂, ∫ t, phk ψ Φ t r₂ * J (fun g => W (g * (uni2 t * hr r₂))) ∂selfDualMeasure ψ ∂LFS.vol2 ψ

def e2r (h : GL (Fin 2) F) : Fin 2 → F := ![h.val 1 0, h.val 1 1]

def cat3 (A : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) : Matrix (Fin 2) (Fin 3) F := !![A 0 0, A 0 1, y 0; A 1 0, A 1 1, y 1]

def pFT (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) : ℂ :=
  ∫ y, Φ (cat3 A y) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ

def zJ (W : GL (Fin 2) F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ := ∫ a, W (dg2 a 1) * ((μ a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F
def zJ' (W : GL (Fin 2) F → ℂ) (ω μ : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ a, W (dg2 a 1 * w0) * (((ω a * μ a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F

def tr2 (V : GL (Fin 2) F → ℂ) (g : GL (Fin 2) F) : GL (Fin 2) F → ℂ := fun h => V (h * g)

def dl : GL (Fin 2) F := dg2 (-1) 1

def e1r (h : GL (Fin 2) F) : Fin 2 → F := ![h.val 0 0, h.val 0 1]

def ftP (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (y : Fin 2 → F) : ℂ :=
  ∫ x, φ x * (ψ (x 0 * y 0 + x 1 * y 1) : ℂ) ∂LFS.vol2 ψ
def ftN (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (y : Fin 2 → F) : ℂ :=
  ∫ x, φ x * (ψ (-(x 0 * y 0 + x 1 * y 1)) : ℂ) ∂LFS.vol2 ψ

def matrixFourierTransposeInv (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (A : Matrix (Fin 2) (Fin 2) F) : ℂ :=
  ∫ N : Fin 2 × Fin 2 → F, Φ (Matrix.of fun i j => N (i, j)) * (ψ (∑ i, ∑ j, N (i, j) * A i j) : ℂ)
    ∂Measure.pi fun _ => selfDualMeasure ψ

def dFT (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) : ℂ :=
  ∫ N : Fin 2 × Fin 2 → F, Φ (cat3 (Matrix.of fun i j => N (i, j)) (-ξ)) * (ψ (∑ i, ∑ j, N (i, j) * A i j) : ℂ)
    ∂Measure.pi fun _ => selfDualMeasure ψ

def hI (p : Fˣ × Fˣ × GL (Fin 2) F) : GL (Fin 2) F := dg2 (p.1 * p.2.1) p.2.1 * p.2.2

def z2I (W₀ V : GL (Fin 2) F → ℂ) (φ : (Fin 2 → F) → ℂ) (s : ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) : ℂ :=
  W₀ (hI p) * V (hI p) * φ (e2r (hI p)) * mp p.1 (s - 1) * mp p.2.1 (2 * s)
def Z2 (ψ : AddChar F Circle) (W₀ V : GL (Fin 2) F → ℂ) (φ : (Fin 2 → F) → ℂ) (s : ℂ) : ℂ := ∫ p, z2I W₀ V φ s p ∂mIw ψ

def rprod (φ₀ φ : (Fin 2 → F) → ℂ) (X : Matrix (Fin 2) (Fin 2) F) : ℂ := φ₀ (X 0) * φ (X 1)

def gjPI (φ₀ φ : (Fin 2 → F) → ℂ) (V : GL (Fin 2) F → ℂ) (ν' : Fˣ →* ℂˣ) (s : ℂ) (p : GL (Fin 2) F × Fˣ) : ℂ :=
  rprod φ₀ φ p.1.val * (((ν' (GeneralLinearGroup.det p.1))⁻¹ : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det p.1) (s + 1 / 2) *
    (V (dg2 p.2 1 * p.1) * ((ν' p.2 : ℂˣ) : ℂ) * mp p.2 (s - 1 / 2))

def gjEI (ψ : AddChar F Circle) (φ₀ φ : (Fin 2 → F) → ℂ) (V : GL (Fin 2) F → ℂ) (ν' : Fˣ →* ℂˣ) (s : ℂ)
    (p : GL (Fin 2) F × Fˣ) : ℂ :=
  matrixFourierTransposeInv ψ (rprod φ₀ φ) (tinv p.1).val * (((ν' (GeneralLinearGroup.det p.1))⁻¹ : ℂˣ) : ℂ) *
    mp (GeneralLinearGroup.det p.1) (s - 3 / 2) * (V (dg2 p.2 1 * p.1) * ((ν' p.2 : ℂˣ) : ℂ) * mp p.2 (s - 1 / 2))

def gjP (ψ : AddChar F Circle) (φ₀ φ : (Fin 2 → F) → ℂ) (V : GL (Fin 2) F → ℂ) (ν' : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ g, rprod φ₀ φ g.val * (((ν' (GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (s + 1 / 2) *
    zJ (tr2 V g) ν' s ∂LFS.hG ψ

def gjE (ψ : AddChar F Circle) (φ₀ φ : (Fin 2 → F) → ℂ) (V : GL (Fin 2) F → ℂ) (ν' : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ g, matrixFourierTransposeInv ψ (rprod φ₀ φ) (tinv g).val * (((ν' (GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
    mp (GeneralLinearGroup.det g) (s - 3 / 2) * zJ (tr2 V g) ν' s ∂LFS.hG ψ

def DampedFunctionalEquationAtPoint (ψ : AddChar F Circle) (ω : Fˣ →* ℂˣ) (G : (Fˣ →* ℂˣ) → ℂ → ℂ) (ν : Fˣ →* ℂˣ) (W₀ V : GL (Fin 2) F → ℂ)
    (φ : (Fin 2 → F) → ℂ) (s : ℂ) : Prop :=
  Integrable (z2I W₀ V φ s) (mIw ψ) ∧ Integrable (z2I (dW2 W₀) (dW2 V) (ftP ψ φ) (1 - s)) (mIw ψ) ∧
    Z2 ψ (dW2 W₀) (dW2 V) (ftP ψ φ) (1 - s) = ((ω (-1) : ℂˣ) : ℂ) * G ν s * G ν⁻¹ s * Z2 ψ W₀ V φ s

def dualWhittakerLocal : (GL (Fin 2) F → ℂ) →ₗ[ℂ] (GL (Fin 2) F → ℂ) where
  toFun := dW2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end D

def ForT (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F], AddChar F Circle → (Fˣ →* ℂˣ) → ((Fˣ →* ℂˣ) → ℂ → ℂ) →
      Submodule ℂ (GL (Fin 2) F → ℂ) → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ω G V', IsUnit1 ω → WhT ψ⁻¹ ω G V' → P F ψ ω G V'

def ForS (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F], AddChar F Circle → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → P F ψ

end Ad3.K.GL2LocalData
