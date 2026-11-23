import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.DampedFunctionalEquationAtPoint

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def rWm (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (g : Matrix (Fin 2) (Fin 2) F) :
    (E → ℂ) → E → ℂ :=
  rW χ σ μE lam (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def FTs (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (Φ : E → ℂ) (u : E) : ℂ :=
  ∫ z, Φ z * (χ (Algebra.trace F E (σ u * z)) : ℂ) ∂μE

open Classical in

def piG (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (g : GL (Fin 2) F)
    (Φ : E → ℂ) (x : E) : ℂ :=
  if h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det then
    ((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ μE lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun y => Φ (y * (h.choose : E))) x
  else 0

open Classical in
variable (E) in

def nfib (f : E → ℂ) (a : Fˣ) : ℂ := if h : ∃ t : Eˣ, Algebra.norm F (t : E) = a then f (h.choose : E) else 0

variable (E) in

def SBE : Set (E → ℂ) := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}

def cjA (A : F) (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F := !![g 0 0, A * g 0 1; g 1 0 / A, g 1 1]

end G

section WF

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

variable (E) in

abbrev muE (χ : AddChar F Circle) : Measure E := selfDualMeasure (chE E χ)

variable (E) in

abbrev rWE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (η : Fˣ →* ℂˣ) : Matrix (Fin 2) (Fin 2) F → (E → ℂ) → E → ℂ :=
  rWm χ σ (muE E χ) (lamE E χ η)
variable (E) in
abbrev WcE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (η : Fˣ →* ℂˣ) (c : Eˣ →* ℂˣ) : (E → ℂ) → GL (Fin 2) F → ℂ :=
  Wc χ σ (muE E χ) (lamE E χ η) c
variable (E) in
abbrev piE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (η : Fˣ →* ℂˣ) (c : Eˣ →* ℂˣ) : GL (Fin 2) F → (E → ℂ) → E → ℂ :=
  piG χ σ (muE E χ) (lamE E χ η) c
variable (E) in
abbrev FTE (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) : (E → ℂ) → E → ℂ := FTs χ σ (muE E χ)

variable (F E) in

def FibProp (κ : ℝ) : Prop :=
  ∀ f : E → ℂ, Continuous (fun x : Eˣ => f x) → (∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → f (x * u) = f x) →
    (Integrable (fun x : Eˣ => f x) (multHaar E) ↔ Integrable (nfib E f) (multHaar F)) ∧
      ∫ x : Eˣ, f x ∂multHaar E = κ * ∫ a : Fˣ, nfib E f a ∂multHaar F

end WF

section SP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

abbrev muS (χ : AddChar F Circle) : Measure (F × F) := (selfDualMeasure χ).prod (selfDualMeasure χ)

abbrev rWS (χ : AddChar F Circle) : Matrix (Fin 2) (Fin 2) F → (F × F → ℂ) → F × F → ℂ := rWm χ swapE (muS χ) 1

def piS (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (h : GL (Fin 2) F) (Φ : F × F → ℂ) (x : F × F) : ℂ :=
  ((c₁ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2) *
    rW χ swapE (muS χ) 1 (h.val 0 0 / (h.val).det) (h.val 0 1) (h.val 1 0 / (h.val).det) (h.val 1 1)
      (fun y => Φ (y * ((h.val).det, 1))) x

end SP

def ForEF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E],
    AddChar F Circle → (E ≃ₐ[F] E) → (Fˣ →* ℂˣ) → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 →
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E]
      [BorelSpace E] [Algebra F E], Module.finrank F E = 2 → Continuous (algebraMap F E) →
    ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → P F E χ σ η

def ForES (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] [CharZero F], AddChar F Circle → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] [CharZero F] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → P F χ

end Ad3.K.GL2LocalData
