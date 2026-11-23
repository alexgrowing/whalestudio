import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.IfaceSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section Maps

variable {k r : ℕ}

def xJ (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := P *ᵥ xOne k r z

def cJ (ε : Fin (2 * r + k + 1) → Bool) (x₁ y : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.herm (Jm ε) (g *ᵥ y) x₁

def cJd (x₁ β : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : ℂ := β ⬝ᵥ (g⁻¹ *ᵥ x₁)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def coefX (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w m : H) (g : Mat k r) : ℂ :=
  ⟪w, σ (x₀⁻¹ * g) m⟫_ℂ

def tMap (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (g : Mat k r) : ℂ :=
  ∑ c, cJ ε x₁ (Pi.single c 1) g * coefX σ x₀ w (f c) g

def tMapD (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H)
    (f : Fin (2 * r + k + 1) → H) (g : Mat k r) : ℂ :=
  ∑ c, cJd x₁ (Pi.single c 1) g * coefX σ x₀ w (f c) g

end Maps

section Per

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def per (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) : Vp :=
  sInt μW μN ψ π (fun g => F (P * g * P⁻¹)) ξ x

def eabB (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r) (a b : Fin (2 * r + k + 1)) (f : Mat k r → Vp) :
    Mat k r → Vp :=
  fun g => S7.EabV ε a b (fun y => f (P⁻¹ * y * P)) (P * g * P⁻¹)

end Per

def aExp {n : ℕ} (ε : Fin n → Bool) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))

def GapNeedStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (h : ℝ), pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h →
    1 ≤ S7.q0 ε ∧ hNeed ε < h

def PsiDatumStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    S7.IsHCParam lam → GapAtLeast ε lam h → hNeed ε < h → 1 ≤ S7.q0 ε → S7.IsMu lam μ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (ι : V ≃ₗ[ℂ] T.V),
      IsURepOn (UJset ε) σ ∧ IsDerivedOn ε σ D E ∧ IsKIrrHW ε E (lowK ε lam) V ∧
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) ∧
      (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) ∧
      ∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ

def TMapStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h →
    ∀ (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : V), x₀ ∈ UJset ε →
    ∀ f : Fin (2 * r + k + 1) → D, (∀ c, f c ∈ genSub E V) →
      IsSmoothL2 ε (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) ∧
      (∀ (a b : Fin (2 * r + k + 1)), ∀ g ∈ UJset ε,
        Formalism.REAL.Eab ε a b (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g =
          tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((LemK.tensV E a b f c : D) : H)) g) ∧
      ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, ∀ g ∈ UJset ε,
        ‖Formalism.REAL.Eword ε wd (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g‖ ≤
          C * frob g ^ (1 - aExp ε h)

def TMapDStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h →
    ∀ (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : V), x₀ ∈ UJset ε →
    ∀ f : Fin (2 * r + k + 1) → D, (∀ c, f c ∈ genSub E V) →
      IsSmoothL2 ε (tMapD σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) ∧
      (∀ (a b : Fin (2 * r + k + 1)), ∀ g ∈ UJset ε,
        Formalism.REAL.Eab ε a b (tMapD σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g =
          tMapD σ x₁ x₀ ((w : D) : H) (fun c => ((LemK.tensVd E a b f c : D) : H)) g) ∧
      ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, ∀ g ∈ UJset ε,
        ‖Formalism.REAL.Eword ε wd (tMapD σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g‖ ≤
          C * frob g ^ (1 - aExp ε h)

def PerStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (h : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h →
    (∀ (F : Mat k r → ℂ) (C : ℝ), ContinuousOn F (UJset ε) →
      (∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h)) →
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ ξ : Vp,
        Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) •
          chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN)) ∧
    ∀ F : Mat k r → ℂ, Formalism.REAL.SmoothOnG ε F →
      (∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, ∀ g ∈ UJset ε,
        ‖Formalism.REAL.Eword ε wd F g‖ ≤ C * frob g ^ (1 - aExp ε h)) →
      ∀ (a b : Fin (2 * r + k + 1)), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ ξ : Vp,
        per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (Formalism.REAL.Eab ε a b F) ξ x =
          eabB ε P a b (per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ) x

def CapValStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    S7.IsHCParam lam → GapAtLeast ε lam h → hNeed ε < h → 1 ≤ S7.q0 ε →
    ∀ (ω : ℂ) (m : D), m ∈ genSub E V →
      Capelli.capelliC E ω m = (∏ t, (ω + ((LemK.thV lam t : ℝ) : ℂ))) • m

def EigStatement : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M)
    (S : Submodule ℂ M) (ω : ℝ) (y β : Fin (m + 1) → ℂ) (v : M),
    IsGlRep E → (∀ a b, ∀ x ∈ S, E a b x ∈ S) → (∀ x ∈ S, Capelli.capelliC E (ω : ℂ) x = 0) → v ∈ S →
    Capelli.nnPlus E y (ω : ℂ) v ∈ LemK.Xs (LemK.eeV E) S (-ω) ∧
      Capelli.nnMinus E β (ω : ℂ) v ∈ LemK.Xs (LemK.eeVd E) S (ω - (m : ℝ))

def EvalPStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h → ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w v : V) (ξ : Vp) (s : Fin (2 * r + k + 1)) (g : Mat k r), x₀ ∈ UJset ε →
      g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ j, u j ≠ lam s + 1 / 2) →
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ ((w : D) : H) ((v : D) : H)) ξ g ≠ 0 →
      ∃ y : Fin (2 * r + k + 1) → ℂ,
        per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (tMap ε σ (xJ P z) x₀ ((w : D) : H)
          (fun c' => ((Capelli.nnPlus E y ((-(LemK.thV lam s) : ℝ) : ℂ) (v : D) c' : D) : H))) ξ g ≠ 0

def EvalMStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h → ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w v : V) (ξ : Vp) (s : Fin (2 * r + k + 1)) (g : Mat k r), x₀ ∈ UJset ε →
      g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ j, u j ≠ lam s - 1 / 2) →
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ x₀ ((w : D) : H) ((v : D) : H)) ξ g ≠ 0 →
      ∃ β : Fin (2 * r + k + 1) → ℂ,
        per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (tMapD σ (xJ P z) x₀ ((w : D) : H)
          (fun c' => ((Capelli.nnMinus E β ((-(LemK.thV lam s) : ℝ) : ℂ) (v : D) c' : D) : H))) ξ g ≠ 0

def QuotPStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h → ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w : V) (ξ : Vp) (s : Fin (2 * r + k + 1)) (x : Fin (2 * r + k + 1) → D), x₀ ∈ UJset ε →
      S7.IsHCParam (lam + Pi.single s 1) → GapAtLeast ε (lam + Pi.single s 1) h →
      x ∈ LemK.Xs (LemK.eeV E) (genSub E V) (LemK.thV lam s) →
      (∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
        (tMap ε σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((x c' : D) : H))) ξ g ≠ 0) →
      ∃ (Wf : Submodule ℂ (Mat k r → ℂ)) (W' : Submodule ℂ (smD ε (rreg ε))),
        (∀ F ∈ Wf, ∃ y ∈ LemK.Xs (LemK.eeV E) (genSub E V) (LemK.thV lam s),
          F = tMap ε σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((y c' : D) : H))) ∧
        (∀ v : smD ε (rreg ε), v ∈ W' ↔ ∃ F ∈ Wf, (v : L2 ε) = toL2 ε F) ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam + Pi.single s 1)) W' ∧
        (∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal (lam + Pi.single s 1) : ℂ) • v) ∧
        (∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε)) ∧
        ∀ F ∈ Wf, (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ g = 0) →
          ∀ g ∈ UJset ε, F g = 0

def QuotMStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) (V : Submodule ℂ D)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (ι : V ≃ₗ[ℂ] T.V),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
    (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
    (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) → S7.IsMu lam μ →
    (∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam → GapAtLeast ε lam h → ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ (x₀ : Mat k r) (w : V) (ξ : Vp) (s : Fin (2 * r + k + 1)) (x : Fin (2 * r + k + 1) → D), x₀ ∈ UJset ε →
      S7.IsHCParam (lam - Pi.single s 1) → GapAtLeast ε (lam - Pi.single s 1) h →
      x ∈ LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s) →
      (∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
        (tMapD σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((x c' : D) : H))) ξ g ≠ 0) →
      ∃ (Wf : Submodule ℂ (Mat k r → ℂ)) (W' : Submodule ℂ (smD ε (rreg ε))),
        (∀ F ∈ Wf, ∃ y ∈ LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s),
          F = tMapD σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((y c' : D) : H))) ∧
        (∀ v : smD ε (rreg ε), v ∈ W' ↔ ∃ F ∈ Wf, (v : L2 ε) = toL2 ε F) ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) W' ∧
        (∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal (lam - Pi.single s 1) : ℂ) • v) ∧
        (∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε)) ∧
        ∀ F ∈ Wf, (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ g = 0) →
          ∀ g ∈ UJset ε, F g = 0

def FinStatement : Prop :=
  S0.IntSStatement → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (lam' : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    pOf ε = k + r → qOf ε = r + 1 → StepGap ε r h → S7.IsHCParam lam' → GapAtLeast ε lam' h →
    ∀ (ξ : Vp) (Wf : Submodule ℂ (Mat k r → ℂ)) (W' : Submodule ℂ (smD ε (rreg ε))),
      (∀ F ∈ Wf, ContinuousOn F (UJset ε) ∧ ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h)) →
      (∀ v : smD ε (rreg ε), v ∈ W' ↔ ∃ F ∈ Wf, (v : L2 ε) = toL2 ε F) →
      IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W' →
      (∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v) →
      (∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε)) →
      (∀ F ∈ Wf, (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ g = 0) →
        ∀ g ∈ UJset ε, F g = 0) →
      BesselNZ ε lam' u

def ConvStatement : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M),
    Capelli.tensV E = LemK.tensV E ∧ Capelli.tensVd E = LemK.tensVd E ∧
      Capelli.eeV E = LemK.eeV E ∧ Capelli.eeVd E = LemK.eeVd E

end ReciprocityTheory.ChartRestriction.DS.Lap
