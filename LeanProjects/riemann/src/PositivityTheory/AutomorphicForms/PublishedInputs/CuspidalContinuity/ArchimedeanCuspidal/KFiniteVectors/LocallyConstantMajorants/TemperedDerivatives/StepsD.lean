import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.CrdcTemperate

noncomputable section

open MeasureTheory Matrix LineDeriv

namespace Ad3.K.LC

def eQ (z : ℂ) (a : Fin 2) : M23 × (Fin 2 → ℂ) := (0, fun a' => if a' = a then z else 0)

def crq (a : Fin 2) (p : M23 × (Fin 2 → ℂ)) : ℂ := p.2 a
def crqc (a : Fin 2) (p : M23 × (Fin 2 → ℂ)) : ℂ := (starRingEnd ℂ) (p.2 a)

theorem crqc_temperate (a : Fin 2) : (crqc a).HasTemperateGrowth := by
  have : crqc a = fun p => (Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) a).comp
      (ContinuousLinearMap.snd ℝ M23 (Fin 2 → ℂ)))) p := by
    ext p; simp [crqc]
  rw [this]
  exact ContinuousLinearMap.hasTemperateGrowth _

def mH (r : Fin 2) (i : Fin 3) : Module.End ℂ Sw := (SchwartzMap.smulLeftCLM ℂ (crd r i)).toLinearMap
def mA (r : Fin 2) (i : Fin 3) : Module.End ℂ Sw := (SchwartzMap.smulLeftCLM ℂ (crdc r i)).toLinearMap
def dH (r : Fin 2) (i : Fin 3) : Module.End ℂ Sw := (dz r i).toLinearMap
def dA (r : Fin 2) (i : Fin 3) : Module.End ℂ Sw := (dzb r i).toLinearMap

def mq (a : Fin 2) : Module.End ℂ Sw := (SchwartzMap.smulLeftCLM ℂ (crq a)).toLinearMap
def mqc (a : Fin 2) : Module.End ℂ Sw := (SchwartzMap.smulLeftCLM ℂ (crqc a)).toLinearMap
def dqH (a : Fin 2) : Module.End ℂ Sw :=
  ((2 : ℂ)⁻¹ • (lineDerivOpCLM ℂ Sw (eQ 1 a) - Complex.I • lineDerivOpCLM ℂ Sw (eQ Complex.I a))).toLinearMap
def dqA (a : Fin 2) : Module.End ℂ Sw :=
  ((2 : ℂ)⁻¹ • (lineDerivOpCLM ℂ Sw (eQ 1 a) + Complex.I • lineDerivOpCLM ℂ Sw (eQ Complex.I a))).toLinearMap

def ZetaZeros (a b : Fin 2) : Module.End ℂ Sw := ∑ c : Fin 3, mH a c * dH b c
def RA (a b : Fin 2) : Module.End ℂ Sw := ∑ c : Fin 3, mA a c * dA b c

def CH (a b : Fin 2) : Module.End ℂ Sw := mq b * dqH a
def CA (a b : Fin 2) : Module.End ℂ Sw := mqc b * dqA a

def EqH : Module.End ℂ Sw := ∑ a : Fin 2, mq a * dqH a
def EqA : Module.End ℂ Sw := ∑ a : Fin 2, mqc a * dqA a

def CanonicalCommutationRelations (m d : Fin 2 → Fin 3 → Module.End ℂ Sw) : Prop :=
  (∀ r i s j, m r i * m s j = m s j * m r i) ∧ (∀ r i s j, d r i * d s j = d s j * d r i) ∧
    ∀ r i s j, d r i * m s j = m s j * d r i + if r = s ∧ i = j then 1 else 0

def DCcrH : Prop := CanonicalCommutationRelations mH dH
def DCcrA : Prop := CanonicalCommutationRelations mA dA

def DPeq : Prop := ∀ i j : Fin 3, PH i j = (∑ r, mH r i * dH r j + if i = j then 1 else 0) ∧
  PA i j = (∑ r, mA r i * dA r j + if i = j then 1 else 0)

def DComm : Prop := ∀ a b c d : Fin 2, ZetaZeros a b * CH c d = CH c d * ZetaZeros a b ∧ RA a b * CA c d = CA c d * RA a b

def DQAlg : Prop := ∀ v : ℂ,
  Formalism.REAL.Tm CH (v - 1) 1 1 * Formalism.REAL.Tm CH v 0 0 - Formalism.REAL.Tm CH (v - 1) 0 1 * Formalism.REAL.Tm CH v 1 0 =
            (v - 1) • (EqH + algebraMap ℂ (Module.End ℂ Sw) v) ∧
    Formalism.REAL.Tm CA (v - 1) 1 1 * Formalism.REAL.Tm CA v 0 0 - Formalism.REAL.Tm CA (v - 1) 0 1 * Formalism.REAL.Tm CA v 1 0 =
      (v - 1) • (EqA + algebraMap ℂ (Module.End ℂ Sw) v)

def DTrH : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (a b : Fin 2) (Ψ : Sw),
  sec k (ZetaZeros a b Ψ) = sec k (CH a b Ψ) + if a = b then ((k : ℂ) - 2) • sec k Ψ else 0
def DTrA : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (a b : Fin 2) (Ψ : Sw),
  sec k (RA a b Ψ) = sec k (CA a b Ψ) + if a = b then (-(k : ℂ)) • sec k Ψ else 0

def DEul : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Ψ : Sw,
  sec k (EqH Ψ) = (-(2 * (k : ℂ) - 1)) • sec k Ψ ∧ sec k (EqA Ψ) = (2 * (k : ℂ) - 3) • sec k Ψ

def DDer : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (i j : Fin 3),
  derH i j (sec k Ψ) = sec k (PH i j Ψ) ∧ derA i j (sec k Ψ) = sec k (PA i j Ψ)

def gauK (k : ℕ) (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  (p.1 0 0 * p.1 1 1 - p.1 0 1 * p.1 1 0) ^ (2 * k - 2) *
    (starRingEnd ℂ) (p.2 0 * p.1 0 0 + p.2 1 * p.1 1 0) ^ (4 * k - 4) *
      Complex.exp (-(2 * Real.pi : ℂ) * ((∑ r, ∑ c, ‖p.1 r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 : ℝ) : ℂ))

def DGau : Prop := ∀ k : ℕ, ∃ Ψ : Sw, ∀ p, Ψ p = gauK k p

def DKne : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Ψ : Sw, (∀ p, Ψ p = gauK k p) → sec k Ψ ≠ 0

def DKfd : Prop := StLin → ∀ k : ℕ, 3 ≤ k → ∀ Ψ : Sw, (∀ p, Ψ p = gauK k p) →
  FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ U3, W' = fun g => sec k Ψ (g * o)})

end Ad3.K.LC
