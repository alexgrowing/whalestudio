import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec

open CompanionTheory.RgExh ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def baseCoef {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (D : Submodule ℂ H) (ξ : H) : D →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun u := fun g => ⟪ξ, σ g u⟫_ℂ
  map_add' u v := by funext g; simp [inner_add_right]
  map_smul' c u := by funext g; simp [inner_smul_right]

def tensCoef0 {V : Type} [AddCommGroup V] [Module ℂ V] (c : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n) :
    (Fin n → V) →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun u := fun g => ∑ i, g j i * c (u i) g
  map_add' u v := by
    funext g
    simp only [Pi.add_apply, map_add, mul_add, sum_add_distrib]
  map_smul' a u := by
    funext g
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun i _ => by ring

def tensCoef (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n) :
    (tens X).V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) := tensCoef0 c j

def stepCoef (X : GMod n) (z : ℂ) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n) :
    (step X z).V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  (tensCoef X c j).comp (stepSub X z).subtype

def pathCoef : (X : GMod n) → (X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) → (χ : Fin n → ℂ) → (ss : List (Fin n)) →
    List (Fin n) → ((path X χ ss).V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
  | X, c, _, [], _ => c
  | X, c, χ, s :: ss, js => pathCoef (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) ss js.tail

def IsGrad (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Formalism.REAL.inG ε A ∧ Aᴴ = A ∧ A * A * A = A ∧ A ≠ 0

def Vm (A : Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (Fin n → ℂ) := LinearMap.range (Matrix.toLin' ((1 / 2 : ℂ) • (A * A - A)))

def Wm (A : Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (Fin n → ℂ) := LinearMap.ker (Matrix.toLin' ((1 / 2 : ℂ) • (A * A + A)))

def Keeps (g : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop := S.map (Matrix.toLin' g) = S

theorem keeps_mul {g h : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)} (hg : Keeps g S) (hh : Keeps h S) :
    Keeps (g * h) S := by
  unfold Keeps at *
  rw [Matrix.toLin'_mul, Submodule.map_comp, hh, hg]

theorem keeps_one (S : Submodule ℂ (Fin n → ℂ)) : Keeps 1 S := by
  unfold Keeps
  rw [Matrix.toLin'_one, Submodule.map_id]

theorem keeps_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) {S : Submodule ℂ (Fin n → ℂ)} (hg : Keeps (g : Matrix (Fin n) (Fin n) ℂ) S) :
    Keeps ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) S := by
  unfold Keeps at *
  conv_lhs => rw [← hg]
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one,
    Submodule.map_id]

def PSub (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : Subgroup (S7.UJ ε) where
  carrier := {g | Keeps ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) (Vm A) ∧
    Keeps ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) (Wm A)}
  one_mem' := ⟨keeps_one _, keeps_one _⟩
  mul_mem' := fun ha hb => ⟨keeps_mul ha.1 hb.1, keeps_mul ha.2 hb.2⟩
  inv_mem' := fun {g} ha => ⟨keeps_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ha.1, keeps_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ha.2⟩

def muPar (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (ν : Measure (PSub ε A)) : Measure (S7.UJ ε) :=
  ν.map Subtype.val

def rhoA (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  let j := (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re
  j * ((n : ℝ) - j)

def lineInt (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (x : S7.UJ ε) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ‖f (S7.toM x * NormedSpace.exp ((t : ℂ) • A))‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))

def NSet (ε : Fin n → Bool) {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (c : ι → V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (A : Matrix (Fin n) (Fin n) ℂ) (μ : Measure (S7.UJ ε)) (s : ℝ) : Set V :=
  {u | ∀ i, ∀ᵐ x ∂μ, lineInt ε (c i u) A s x < ⊤}

def famP {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ)
    (ss : List (Fin n)) : D × List (Fin n) → ((path ⟨D, E, hE⟩ χ ss).V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) :=
  fun p => pathCoef ⟨D, E, hE⟩ (baseCoef σ D (p.1 : H)) χ ss p.2

def IsParHaar (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (μ : Measure (S7.UJ ε)) : Prop :=
  ∃ ν : Measure (PSub ε A), μ = muPar ε A ν ∧ ν.IsHaarMeasure

def Start : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    CompanionTheory.D.LK.IsKMod ε σ D E → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsSqIntOn ε σ →
    ∀ A μ, IsGrad ε A → IsParHaar ε A μ → ∀ u : D, u ∈ NSet ε (fun ξ : H => baseCoef σ D ξ) A μ (-rhoA A)

def Labels : Prop :=
  StepChar → ∀ n : ℕ, ∃ B : ℝ, ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → HasChar ⟨D, E, hK.gl⟩ χ → GoodPath χ ss →
    FarLabels χ (pathEnd χ ss) B → ∀ A μ, IsGrad ε A → IsParHaar ε A μ →
    (∀ u : D, u ∈ NSet ε (fun ξ : D => baseCoef σ D (ξ : H)) A μ (-rhoA A)) →
      ∀ u, u ∈ NSet ε (famP σ D E hK.gl χ ss) A μ (-rhoA A - 1)

def Back : Prop :=
  StepChar → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsSqIntOn ε σ → HasChar ⟨D, E, hK.gl⟩ χ →
    (∀ A μ, IsGrad ε A → IsParHaar ε A μ → ∀ u, u ∈ NSet ε (famP σ D E hK.gl χ ss) A μ (-rhoA A - 1)) →
      L2Embedding ε (path ⟨D, E, hK.gl⟩ χ ss)

end CompanionTheory.RgExh.Dec
