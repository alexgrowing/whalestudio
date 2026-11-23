import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

noncomputable section

open MeasureTheory Matrix LineDeriv

namespace Ad3.K.LC

def eU (z : ℂ) (r : Fin 2) (c : Fin 3) : M23 × (Fin 2 → ℂ) := (fun r' c' => if r' = r ∧ c' = c then z else 0, 0)

def pol (i j : Fin 3) (X : M23) : M23 := fun r c => if c = j then X r i else 0

def crd (r : Fin 2) (i : Fin 3) (p : M23 × (Fin 2 → ℂ)) : ℂ := p.1 r i

def crdc (r : Fin 2) (i : Fin 3) (p : M23 × (Fin 2 → ℂ)) : ℂ := (starRingEnd ℂ) (p.1 r i)

theorem crd_temperate (r : Fin 2) (i : Fin 3) : (crd r i).HasTemperateGrowth := by
  have : crd r i = fun p => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 3 → ℂ) r).comp
        (ContinuousLinearMap.fst ℝ M23 (Fin 2 → ℂ)))) p := by
    ext p; simp [crd]
  rw [this]
  exact ContinuousLinearMap.hasTemperateGrowth _

theorem crdc_temperate (r : Fin 2) (i : Fin 3) : (crdc r i).HasTemperateGrowth := by
  have : crdc r i = fun p => (Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 3 → ℂ) r).comp
        (ContinuousLinearMap.fst ℝ M23 (Fin 2 → ℂ))))) p := by
    ext p; simp [crdc]
  rw [this]
  exact ContinuousLinearMap.hasTemperateGrowth _

def dz (r : Fin 2) (c : Fin 3) : Sw →L[ℂ] Sw :=
  (2 : ℂ)⁻¹ • (lineDerivOpCLM ℂ Sw (eU 1 r c) - Complex.I • lineDerivOpCLM ℂ Sw (eU Complex.I r c))
def dzb (r : Fin 2) (c : Fin 3) : Sw →L[ℂ] Sw :=
  (2 : ℂ)⁻¹ • (lineDerivOpCLM ℂ Sw (eU 1 r c) + Complex.I • lineDerivOpCLM ℂ Sw (eU Complex.I r c))

def PHc (i j : Fin 3) : Sw →L[ℂ] Sw :=
  (∑ r : Fin 2, (SchwartzMap.smulLeftCLM ℂ (crd r i)).comp (dz r j)) + if i = j then ContinuousLinearMap.id ℂ Sw else 0

def PAc (i j : Fin 3) : Sw →L[ℂ] Sw :=
  (∑ r : Fin 2, (SchwartzMap.smulLeftCLM ℂ (crdc r i)).comp (dzb r j)) + if i = j then ContinuousLinearMap.id ℂ Sw else 0

def PH (i j : Fin 3) : Module.End ℂ Sw := (PHc i j).toLinearMap
def PA (i j : Fin 3) : Module.End ℂ Sw := (PAc i j).toLinearMap

def HasDer : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (g : GL (Fin 3) ℂ), ∃ L : complexMatrix3 →L[ℝ] ℂ,
  HasFDerivAt (extC (sec k Ψ)) L (Matrix.of.symm (g : Matrix (Fin 3) (Fin 3) ℂ)) ∧
    ∀ m : complexMatrix3, L m = ∑ i, ∑ j, ((((g⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.of m) i j * sec k (PH i j Ψ) g +
      (starRingEnd ℂ) ((((g⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) * Matrix.of m) i j) * sec k (PA i j Ψ) g)

end Ad3.K.LC
