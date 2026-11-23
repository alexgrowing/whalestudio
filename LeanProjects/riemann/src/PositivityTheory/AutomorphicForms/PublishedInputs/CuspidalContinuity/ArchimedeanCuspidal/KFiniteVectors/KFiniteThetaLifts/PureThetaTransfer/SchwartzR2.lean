import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import GroundTheory.HeightsAndTheta.Theta.WeilBox

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic ComplexConjugate
open scoped ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

section C

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def bM (M : Matrix (Fin 2) (Fin 2) F) (x y : Fin 2 → F) : F := x ⬝ᵥ M *ᵥ y

def nM (M : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F) : F := bM M x x / 2

def muM (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) : Measure (Fin 2 → F) :=
  ENNReal.ofReal ((modulus M.det : ℝ) ^ (1 / 2 : ℝ)) • GroundTheory.Heights₂.Theta.selfDualPi (ι := Fin 2) χ

def FTb (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (Φ : (Fin 2 → F) → ℂ) (y : Fin 2 → F) : ℂ :=
  ∫ x, Φ x * (χ (bM M y x) : ℂ) ∂muM χ M

open Classical in

def rWC (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ) (a b c d : F)
    (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F) : ℂ :=
  if c = 0 then (χ (a * b * nM M z) : ℂ) * eta a * ((modulus a : ℝ) : ℂ) * Φ (a • z)
  else lam * eta (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
    ∫ u, (χ ((a * nM M z + d * nM M u - bM M z u) / c) : ℂ) * Φ u ∂muM χ M

def rWCm (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ) (g : Matrix (Fin 2) (Fin 2) F) :
    ((Fin 2 → F) → ℂ) → (Fin 2 → F) → ℂ :=
  rWC χ M lam eta (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def SBC : Set ((Fin 2 → F) → ℂ) := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}

end C

def ForF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F], Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F], P F

def RCN : Prop := ForF fun F _ _ _ _ _ _ => ∀ (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ)
  (a b c d x : F), a * d - b * c = 1 → ∀ (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F),
    rWC χ M lam eta (a + x * c) (b + x * d) c d Φ z = (χ (x * nM M z) : ℂ) * rWC χ M lam eta a b c d Φ z

def RCM : Prop := ForF fun F _ _ _ _ _ _ => ∀ (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ),
  (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) → (∀ x : F, x ≠ 0 → eta x * eta x = 1) →
  ∀ (a b c d : F), a * d - b * c = 1 → ∀ (t : Fˣ) (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F),
    rWC χ M lam eta ((t : F) * a) ((t : F) * b) (c / t) (d / t) Φ z =
      eta t * ((modulus (t : F) : ℝ) : ℂ) * rWC χ M lam eta a b c d Φ ((t : F) • z)

def RCT : Prop := ForF fun F _ _ _ _ _ _ => ∀ (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ),
  M.det ≠ 0 → ∀ m : Matrix (Fin 2) (Fin 2) F, mᵀ * M * m = M → ∀ (a b c d : F) (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F),
    rWC χ M lam eta a b c d (fun x => Φ (m *ᵥ x)) z = rWC χ M lam eta a b c d Φ (m *ᵥ z)

def TRANS : Prop := ForF fun F _ _ _ _ _ _ => ∀ (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] [BorelSpace E] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ)
  (M : Matrix (Fin 2) (Fin 2) F) (j : (Fin 2 → F) ≃ₗ[F] E), Continuous j → Continuous j.symm →
  (∀ x, Algebra.norm F (j x) = nM M x) → (∀ x y, Algebra.trace F E (σ (j x) * j y) = bM M x y) →
  Measure.map j (muM χ M) = μE → ∀ (a b c d : F) (Φ : E → ℂ) (z : Fin 2 → F),
    rWC χ M lam (GL2LocalData.nsg E) a b c d (fun x => Φ (j x)) z = GL2LocalData.rW χ σ μE lam a b c d Φ (j z)

def REPC : Prop := ForF fun F _ _ _ _ _ _ => ∀ (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] [BorelSpace E] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ)
  (M : Matrix (Fin 2) (Fin 2) F) (j : (Fin 2 → F) ≃ₗ[F] E), Continuous j → Continuous j.symm →
  (∀ x, Algebra.norm F (j x) = nM M x) → (∀ x y, Algebra.trace F E (σ (j x) * j y) = bM M x y) →
  Measure.map j (muM χ M) = μE →
  (∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Φ ∈ GL2LocalData.SBE E,
    GL2LocalData.rWm χ σ μE lam h Φ ∈ GL2LocalData.SBE E ∧ GL2LocalData.rWm χ σ μE lam (g * h) Φ = GL2LocalData.rWm χ σ μE lam g (GL2LocalData.rWm χ σ μE lam h Φ)) →
  ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Φ ∈ (SBC : Set ((Fin 2 → F) → ℂ)),
    rWCm χ M lam (GL2LocalData.nsg E) h Φ ∈ (SBC : Set ((Fin 2 → F) → ℂ)) ∧
      rWCm χ M lam (GL2LocalData.nsg E) (g * h) Φ = rWCm χ M lam (GL2LocalData.nsg E) g (rWCm χ M lam (GL2LocalData.nsg E) h Φ)

def RCWF : Prop := ForF fun F _ _ _ _ _ _ => ∀ (χ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (lam : ℂ) (eta : F → ℂ),
  eta 1 = 1 → M.IsSymm → ∀ (Φ : (Fin 2 → F) → ℂ) (z : Fin 2 → F),
    rWCm χ M lam eta !![0, 1; -1, 0] Φ z = lam * FTb χ M Φ z

def bMR (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2 → ℝ) : ℝ := x ⬝ᵥ M *ᵥ y

def nMR (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ℝ := bMR M x x / 2

def muMR (M : Matrix (Fin 2) (Fin 2) ℝ) : Measure (Fin 2 → ℝ) := ENNReal.ofReal (|M.det| ^ (1 / 2 : ℝ)) • volume

def rWCR (M : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℂ) (eta : ℝ → ℂ) (a b c d : ℝ) (Φ : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  if c = 0 then
    Complex.exp (2 * Real.pi * Complex.I * ((a * b * nMR M z : ℝ) : ℂ)) * eta a * ((|a| : ℝ) : ℂ) * Φ (a • z)
  else lam * eta (-c) * ((|c|⁻¹ : ℝ) : ℂ) *
    ∫ u, Complex.exp (2 * Real.pi * Complex.I * (((a * nMR M z + d * nMR M u - bMR M z u) / c : ℝ) : ℂ)) * Φ u ∂muMR M

def rWCRm (M : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℂ) (eta : ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ((Fin 2 → ℝ) → ℂ) → (Fin 2 → ℝ) → ℂ :=
  rWCR M lam eta (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def schwartzR2 : Set ((Fin 2 → ℝ) → ℂ) := {Φ | ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ, ∀ x, f (WithLp.toLp 2 x) = Φ x}

def TRANSR : Prop := ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (j : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ),
  (∀ x, Complex.normSq (j x) = nMR M x) → (∀ x y, 2 * (conj (j x) * j y).re = bMR M x y) →
  Measure.map j (muMR M) = volC → ∀ (a b c d : ℝ) (Φ : ℂ → ℂ) (z : Fin 2 → ℝ),
    rWCR M Complex.I sgR a b c d (fun x => Φ (j x)) z = rWR a b c d Φ (j z)

def REPCR : Prop := RWRREP → ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (j : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ),
  (∀ x, Complex.normSq (j x) = nMR M x) → (∀ x y, 2 * (conj (j x) * j y).re = bMR M x y) →
  Measure.map j (muMR M) = volC → ∀ g h : Matrix (Fin 2) (Fin 2) ℝ, g.det = 1 → h.det = 1 → ∀ Φ ∈ schwartzR2,
    rWCRm M Complex.I sgR h Φ ∈ schwartzR2 ∧ rWCRm M Complex.I sgR (g * h) Φ = rWCRm M Complex.I sgR g (rWCRm M Complex.I sgR h Φ)

end Ad3.K.QuadraticBaseChangeGL3.Th
