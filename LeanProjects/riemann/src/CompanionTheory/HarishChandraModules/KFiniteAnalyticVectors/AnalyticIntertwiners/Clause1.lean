import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FinalExists

open Matrix

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS
open Formalism.BasicNotions.TH (GrpData URep GKMod)

section

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def KF (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set (smD ε σ) :=
  {v | Formalism.MainNotions.S.IsKFin ε σ (v : H)}

def wd (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (W : List (Matrix (Fin n) (Fin n) ℂ)) :
    Module.End ℂ (smD ε σ) := (W.map (actM (smE ε σ))).prod

def l1 (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖

end

def ForIrr (P : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    (Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → P n ε H σ

def KFSm : Prop := ForIrr fun _ ε H _ _ σ =>
  (∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v → v ∈ smD ε σ) ∧ ∀ a b, ∀ v ∈ KF ε σ, smE ε σ a b v ∈ KF ε σ

def CasScal : Prop := ForIrr fun _ ε _ _ _ σ => ∃ c : ℝ, ∀ v : smD ε σ, casimir (smE ε σ) v = (c : ℂ) • v

def IntWts : Prop := ForIrr fun n ε _ _ _ σ => ∀ v ∈ KF ε σ, v ∈ Submodule.span ℂ
  {w : smD ε σ | w ∈ KF ε σ ∧ ∃ μ : Fin n → ℤ, ∀ a, smE ε σ a a w = (μ a : ℂ) • w}

def WordBd : Prop := ForIrr fun n ε H _ _ σ => ∀ v ∈ KF ε σ, ∃ C : ℝ, 0 < C ∧ ∀ W : List (Matrix (Fin n) (Fin n) ℂ),
  ‖((wd ε σ W v : smD ε σ) : H)‖ ≤ C ^ (W.length + 1) * W.length.factorial * (W.map l1).prod

def UIrr : Prop := ForIrr fun _ ε _ _ _ σ => ∀ N : Submodule ℂ (smD ε σ), (N : Set (smD ε σ)) ⊆ KF ε σ →
  (∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N) → N = ⊥ ∨ (N : Set (smD ε σ)) = KF ε σ

def UAdm : Prop := ForIrr fun n ε _ _ _ σ => ∀ μ : Fin n → ℝ, FiniteDimensional ℂ (Submodule.span ℂ
  {v : smD ε σ | v ∈ KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v})

def epq (p q : ℕ) : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft

def rx {p q : ℕ} (X : Formalism.BasicNotions.TH.Mat p q) : Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv X

def IsTw {p q : ℕ} {T : GrpData p q} (πU : URep T) (j : ℕ)
    (σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)) : Prop :=
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ ∧
    ∀ x : T.G, πU.π x = (((T.sq x : ℂˣ) : ℂ) ^ j) • σ (rx ((T.cov x : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q))

def Descend : Prop :=
  ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T), Formalism.MainNotions.SchurIrreducible.IrrU πU →
    ∃ (j : ℕ) (σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)), IsTw πU j σ ∧
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset (epq p q)) σ ∧
      (∀ x, Formalism.BasicNotions.TH.KFin T πU.π x ↔ Formalism.MainNotions.S.IsKFin (epq p q) σ x) ∧
      ∀ X ∈ Formalism.BasicNotions.TH.upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
        πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X))

def Clause1 : Prop :=
  ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (πU : URep T), Formalism.MainNotions.SchurIrreducible.IrrU πU →
    (∀ x, Formalism.BasicNotions.TH.KFin T πU.π x → Formalism.BasicNotions.TH.Smooth T πU.π x) ∧
    (∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), Formalism.MainNotions.SchurIrreducible.IsHCMod πU M io) ∧
    ∀ (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), Formalism.MainNotions.SchurIrreducible.IsHCMod πU M io → Formalism.MainNotions.SchurIrreducible.AdmGK M ∧ Formalism.MainNotions.SchurIrreducible.IrrGK M

def Clause2 : Prop :=
  ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (π₁ π₂ : URep T), Formalism.MainNotions.SchurIrreducible.IrrU π₁ → Formalism.MainNotions.SchurIrreducible.IrrU π₂ →
    ∀ (M₁ M₂ : GKMod p q) (io₁ : M₁.V →ₗ[ℂ] π₁.H) (io₂ : M₂.V →ₗ[ℂ] π₂.H),
      Formalism.MainNotions.SchurIrreducible.IsHCMod π₁ M₁ io₁ → Formalism.MainNotions.SchurIrreducible.IsHCMod π₂ M₂ io₂ →
      ∀ e : M₁.V ≃ₗ[ℂ] M₂.V, (∀ Z v, e (M₁.act Z v) = M₂.act Z (e v)) →
      ∃ U : π₁.H ≃ₗᵢ[ℂ] π₂.H, ∀ g x, U (π₁.π g x) = π₂.π g (U x)

def Clause3 : Prop :=
  ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (πU : URep T) (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H),
    Formalism.MainNotions.SchurIrreducible.IsHCMod πU M io → Formalism.MainNotions.SchurIrreducible.AdmGK M → Formalism.MainNotions.SchurIrreducible.IrrGK M → Formalism.MainNotions.SchurIrreducible.IrrU πU

theorem hcm_of (h1 : Clause1) (h2 : Clause2) (h3 : Clause3) (h4 : GlobalTheory.Published.KFiniteAnalyticUJ) :
    GlobalTheory.Published.HarishChandraModules :=
  ⟨fun p q h T => ⟨h1 p q h T, h2 p q h T, h3 p q h T⟩, h4⟩

end CompanionTheory.D.gk.HC
