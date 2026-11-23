import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsHWSmooth

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

def PairingPropertiesStatement : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ P : Mat k r, Formalism.MainNotions.S.IsCayley k r (parEps k r) P ∧ WCols k r P ∧
    (∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r),
      trace (dMat (dNode k r) * (P * Y * P⁻¹)) =
        ∑ a, (Formalism.MainNotions.S.ellA k r (z0 k r) Y a - starRingEnd ℂ (Formalism.MainNotions.S.ellA k r (z0 k r) Y a))) ∧
    ∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), ∀ t : ℝ,
      Formalism.MainNotions.S.psiGen k r (z0 k r) (cBase r t) (NormedSpace.exp Y) =
        Complex.exp ((t : ℂ) * trace (dMat (dNode k r) * (P * Y * P⁻¹)))

def RaisingLoweringNormIdentities : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (w : M), IsHWDatum ε E lam w →
    (∀ a b, a < b → ε a = ε b → ‖E b a w‖ ^ 2 = lowK ε lam a - lowK ε lam b) ∧
    (∀ a b, a < b → ε a ≠ ε b → ‖E a b w‖ ^ 2 = ‖E b a w‖ ^ 2 + (lowK ε lam a - lowK ε lam b)) ∧
    2 * ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), ‖E b a w‖ ^ 2 =
      nsq (rho n) - nsq (rhoN ε - rhoC ε)

def HighestWeightVectorUniformBounds : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d Λ₀ : Fin n → ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, 1 ≤ t → ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
      (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (w : M), IsHWDatum ε E lam w →
      lowK ε lam = t • d + Λ₀ →
      (∀ a b, InNP ε d a b → ‖E a b w‖ ≤ C) ∧
      (∀ a b, InLL ε d a b → ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ C) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        ‖actM E X w - ((t : ℂ) * trace (dMat d * X)) • w‖ ≤ C * Real.sqrt t * l1 X

def SmInfUnitaryStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsInfUnitary ε (smE ε σ)

def MatrixCoeffConjugationMove : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), IsURepOn (UJset ε) σ → w ∈ smD ε σ →
    ∀ g ∈ UJset ε, ∀ X : Matrix (Fin n) (Fin n) ℂ,
      ⟪w, σ g (phiW ε σ w X)⟫_ℂ = ⟪phiW ε σ w (stJ ε (g * X * g⁻¹)), σ g w⟫_ℂ

def DerivMatrixCoeffExp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), IsURepOn (UJset ε) σ → w ∈ smD ε σ →
    ∀ Z, inG ε Z → ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => ⟪w, σ (NormedSpace.exp ((s : ℂ) • Z)) w⟫_ℂ)
        ⟪w, σ (NormedSpace.exp ((s : ℂ) • Z)) (phiW ε σ w Z)⟫_ℂ s

section Taylor

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ConjugationSecondOrderBound : Prop :=
  ∀ (n : ℕ) (R : ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ Y M : Matrix (Fin n) (Fin n) ℂ, ‖Y‖ ≤ R → ‖M‖ ≤ R →
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      ‖NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
          (τ : ℂ) • (Y * M - M * Y)‖ ≤ K * τ ^ 2

end Taylor

def TangentPairingStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d Λ₀ : Fin n → ℝ) (R : ℝ), ∃ C : ℝ,
    ∀ t : ℝ, 1 ≤ t → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsHWSmooth ε σ lam w →
      lowK ε lam = t • d + Λ₀ → ∀ Y, inG ε Y → S7.hs Y ≤ R ^ 2 →
        ‖⟪w, σ (NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • Y)) w⟫_ℂ *
            Complex.exp (-((Real.sqrt t : ℂ) * trace (dMat d * Y))) -
          Complex.exp (-(qForm ε d Y) / 2)‖ ≤ C / Real.sqrt t

def MatrixCoeffBoundsImplyBound : Prop :=
  HighestWeightVectorUniformBounds → MatrixCoeffConjugationMove → DerivMatrixCoeffExp → ConjugationSecondOrderBound → SmInfUnitaryStatement → TangentPairingStatement

def NsetExpInjectiveSurjective : Prop :=
  ∀ k r : ℕ,
    (∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), ∀ Y' ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r),
      NormedSpace.exp Y = NormedSpace.exp Y' → Y = Y') ∧
    (∀ g ∈ Formalism.QuantumDeterminants.Nset k r, ∃ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), NormedSpace.exp Y = g) ∧
    (∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) ∧
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) ∧
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r),
      Real.sqrt (S7.hs Y) ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
        (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m

def CayleyMajorantBound : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P →
    ∃ c : ℝ, 0 < c ∧ ∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), ∀ (κ : S7.KG ε) (X : Mat k r), inP ε X →
      P * NormedSpace.exp Y * P⁻¹ = S7.toMK κ * NormedSpace.exp X →
      c * Real.log (1 + S7.hs Y) ≤ min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * (S7.q0 ε : ℝ)))

def GaussianLimitHaar : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (f : ℕ → E → ℂ),
    (∀ᶠ t : ℕ in atTop, AEStronglyMeasurable (f t) μ) → ∀ B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ,
    (∀ v, Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-(B v v))))) →
    ∀ {c γ : ℝ}, 0 < c → 0 < γ →
    (∀ᶠ t : ℕ in atTop, ∀ v, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) →
    ∀ᶠ t : ℕ in atTop, Integrable (f t) μ ∧ ∫ v, f t v ∂μ ≠ 0

def ExistsUnitaryHaarProbability : Prop :=
  ∀ k r : ℕ, ∃ μW : Measure (Formalism.QuantumDeterminants.Mt k r),
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r (z0 k r)) μW ∧ μW Set.univ = 1

def WhittakerSchurOrthogonality : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (Λ : Fin (2 * r + k + 1) → ℝ) (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r) (u : Fin k → ℝ) (c : Fin r → ℂ)
    (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)) (ξ : Vp) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    1 ≤ k → Formalism.MainNotions.S.IsCayley k r ε P → WCols k r P →
    Formalism.MainNotions.S.IsHCTypeU k u (fun h => π (Formalism.MainNotions.S.blockW k r h)) → ‖ξ‖ = 1 →
    Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) (fun h => π (Formalism.MainNotions.S.blockW k r h))
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ →
    (∀ a : Fin k, Λ ⟨a.val, by omega⟩ = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a) →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r (z0 k r)) μW → μW Set.univ = 1 → SigmaFinite μN →
    ContinuousOn (S7.PsiM T μ) (UJset ε) →
    Integrable (fun m : Formalism.QuantumDeterminants.Mt k r => ‖S7.PsiM T μ (P * Matrix.of m * P⁻¹)‖) μN →
    ⟪ξ, aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r (z0 k r) c) π T.w T.w ξ 1 1⟫_ℂ =
      (Module.finrank ℂ Vp : ℂ)⁻¹ *
        ∫ m, psiCoef T μ P T.w T.w (Matrix.of m) *
          starRingEnd ℂ (Formalism.MainNotions.S.psiGen k r (z0 k r) c (Matrix.of m)) ∂μN

def LamTStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b →
    Formalism.QuantumDeterminants.IsHCParam u ∧ 1 ≤ S7.q0 (parEps k r) ∧
    (∀ t : ℕ, lowK (parEps k r) (lamT k r u b t) =
      (t : ℝ) • dNode k r + lowK (parEps k r) (lamT k r u b 0)) ∧
    (∀ (t : ℕ) (a : Fin k), lowK (parEps k r) (lamT k r u b t) ⟨a.val, by omega⟩ =
      Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a) ∧
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → S7.IsHCParam (lamT k r u b t) ∧
      GapLap (parEps k r) (lamT k r u b t) ((t : ℝ) / 2)

def StepIBaseStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b →
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → BesselNZ (parEps k r) (lamT k r u b t) u

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
