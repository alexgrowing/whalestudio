import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdealStatement

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Dec.J

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

variable {n : ℕ}

structure Filt (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) where
  N : ℝ → Submodule ℂ X.V
  mono : ∀ s s', s ≤ s' → N s ≤ N s'
  top : ∃ s, N s = ⊤
  shift : ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℤ), A * Y - Y * A = (k : ℂ) • Y →
    ∀ s, ∀ u ∈ N s, actM X.E Y u ∈ N (s + k)
  eig : ∀ s s', s' < s → N s = ⊤ → ∀ (z : ℂ) (u : X.V), u ∉ N s' → actM X.E A u - z • u ∈ N s' →
    s' ≤ z.re ∧ z.re < s

def contraE (X : GMod n) (a b : Fin n) : Module.End ℂ (Module.Dual ℂ X.V) := -(X.E a b).dualMap

def W {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt X A) : Submodule ℂ (Module.Dual ℂ X.V) where
  carrier := {φ | ∃ s, ∀ u ∈ F.N s, φ u = 0}
  add_mem' := by
    rintro φ ψ ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨min s t, fun u hu => ?_⟩
    simp [hs u (F.mono _ _ (min_le_left s t) hu), ht u (F.mono _ _ (min_le_right s t) hu)]
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c φ ⟨s, hs⟩
    exact ⟨s, fun u hu => by simp [hs u hu]⟩

def dims (n j : ℕ) : Fin 3 → ℕ := ![j, n - 2 * j, j]

structure GradBasis (A : Matrix (Fin n) (Fin n) ℂ) where
  U : Matrix (Fin n) (Fin n) ℂ
  Ui : Matrix (Fin n) (Fin n) ℂ
  hU : U * Ui = 1
  hUi : Ui * U = 1
  j : ℕ
  hj : ∑ i, dims n j i = n
  eq : A = U * Matrix.diagonal (fun p => ((![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n j) hj).symm p).1)) * Ui

def bl {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (p : Fin n) : Fin 3 := ((stdBlocks (dims n B.j) B.hj).symm p).1

def Eb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (p q : Fin n) : Module.End ℂ X.V :=
  actM X.E (B.U * Matrix.single p q 1 * B.Ui)

def Qb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (i : Fin 3) (Y : ℂ) : Module.End ℂ X.V :=
  qdet (fun p q : Fin (dims n B.j i) => Eb X B (stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (stdBlocks (dims n B.j) B.hj ⟨i, q⟩))
    (Y + ((dims n B.j i : ℂ) - 1) / 2 - (modExp (fun i => Fin (dims n B.j i)) i : ℂ) / 2)

def IsLabel (j : ℕ) (L : Fin n → Fin 3) : Prop := ∀ i, (univ.filter fun s => L s = i).card = dims n j i

def plab (χ : Fin n → ℂ) (L : Fin n → Fin 3) (i : Fin 3) (Y : ℂ) : ℂ := ∏ s ∈ univ.filter (fun s => L s = i), (Y + χ s)

def deg (χ : Fin n → ℂ) (L : Fin n → Fin 3) : ℂ :=
  ∑ s ∈ univ.filter (fun s => L s = 2), χ s - ∑ s ∈ univ.filter (fun s => L s = 0), χ s

def PP {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt X A) (B : GradBasis A) (χ : Fin n → ℂ)
    (Λ : Set (Fin n → Fin 3)) : Prop :=
  ∀ W' : Submodule ℂ (Module.Dual ℂ X.V), W' ≤ W F → (∀ a b, ∀ φ ∈ W', contraE X a b φ ∈ W') → W' ≠ W F →
    ∃ φ ∈ W F, φ ∉ W' ∧ (∀ p q, bl B p < bl B q → (Eb X B p q).dualMap φ ∈ W') ∧
      ∃ L ∈ Λ, IsLabel B.j L ∧ ∀ i Y, φ ∘ₗ Qb X B i Y - plab χ L i Y • φ ∈ W'

def move (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)) (s : Fin n) : Set (Fin n → Fin 3) :=
  {L' | ∃ L ∈ Λ, ∃ r, χ r = χ s ∧ L' = L ∘ Equiv.swap r s}

def SandStep {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt X A) (z : ℂ) (F'' : Filt (step X z) A) : Prop :=
  ∀ s (u : stepSub X z), ((∀ i, (u : Fin n → X.V) i ∈ F.N (s - 1)) → u ∈ F''.N s) ∧
    (u ∈ F''.N s → ∀ i, (u : Fin n → X.V) i ∈ F.N (s + 1))

def IsCoefFam (ε : Fin n → Bool) (X : GMod n) {ι : Type} (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Prop :=
  (∀ i u (Y : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Y → ∀ g, Formalism.REAL.inUJ ε g →
    HasDerivAt (fun t : ℝ => c i u (g * NormedSpace.exp ((t : ℂ) • Y))) (c i (actM X.E Y u) g) 0) ∧
  ∀ i, ∃ l : Fin n → Fin n → ι →₀ ℂ, ∀ (a b : Fin n) (u : X.V) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
    c i (X.E a b u) g = ∑ c', ∑ d, (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c' d *
      (l c' d).sum fun i' r => r * c i' u g

def moveIter : (Fin n → ℂ) → Set (Fin n → Fin 3) → List (Fin n) → Set (Fin n → Fin 3)
  | _, Λ, [] => Λ
  | χ, Λ, s :: ss => moveIter (χ + Pi.single s 1) (move χ Λ s) ss

def TensDecomp : Prop :=
  ∀ (n : ℕ) (X : GMod n) (χ : Fin n → ℂ), HasChar X χ → ⨆ r, stepSub X (χ r) = ⊤

def ConjQdet : Prop :=
  ∀ (n : ℕ) (X : GMod n) (U Ui : Matrix (Fin n) (Fin n) ℂ), U * Ui = 1 → Ui * U = 1 → ∀ u : ℂ,
    qdet (fun p q => actM X.E (U * Matrix.single p q 1 * Ui)) u = qdet X.E u

def LocFinA {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt X A) : Prop :=
  ∀ t : ℝ, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ u : X.V, Polynomial.aeval (actM X.E A) q u ∈ F.N t

def Start1 : Prop :=
  ∀ (n : ℕ) (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (F : Filt X A) (B : GradBasis A) (χ : Fin n → ℂ),
    LocFinA F → HasChar X χ → F.N (-rhoA A) = ⊤ → PP F B χ {L | IsLabel B.j L ∧ (deg χ L).re < 0}

def Transport : Prop :=
  StepChar → TensDecomp → ∀ (n : ℕ) (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (F : Filt X A) (B : GradBasis A) (χ : Fin n → ℂ) (s : Fin n)
    (F'' : Filt (step X (χ s)) A) (Λ : Set (Fin n → Fin 3)),
    HasChar X χ → (∀ r, χ r ≠ χ s + 1) → SandStep F (χ s) F'' → PP F B χ Λ → PP F'' B (χ + Pi.single s 1) (move χ Λ s)

def Degree : Prop :=
  ∀ (n : ℕ) (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (F : Filt X A) (B : GradBasis A) (χ : Fin n → ℂ)
    (Λ : Set (Fin n → Fin 3)) (c : ℝ), LocFinA F → HasChar X χ → PP F B χ Λ → (∀ L ∈ Λ, (deg χ L).re < c + rhoA A) → F.N c = ⊤

def LocFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (F : Filt X A) (χ : Fin n → ℂ),
    IsGrad ε A → HasChar X χ → LocFinA F

def Basis : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A → Nonempty (GradBasis A)

def FamFilt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (ι : Type) (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : MeasureTheory.Measure (ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)),
    IsCoefFam ε X c → IsGrad ε A → IsParHaar ε A μ → (∃ s, ∀ u, u ∈ NSet ε c A μ s) →
      ∃ F : Filt X A, ∀ s u, u ∈ F.N s ↔ u ∈ NSet ε c A μ s

def StepFam : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (ι : Type) (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (z : ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : MeasureTheory.Measure (ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)),
    IsCoefFam ε X c → IsGrad ε A →
      IsCoefFam ε (step X z) (fun p : ι × Fin n => stepCoef X z (c p.1) p.2) ∧
      ∀ s (u : stepSub X z),
        ((∀ i, (u : Fin n → X.V) i ∈ NSet ε c A μ (s - 1)) → u ∈ NSet ε (fun p : ι × Fin n => stepCoef X z (c p.1) p.2) A μ s) ∧
        (u ∈ NSet ε (fun p : ι × Fin n => stepCoef X z (c p.1) p.2) A μ s → ∀ i, (u : Fin n → X.V) i ∈ NSet ε c A μ (s + 1))

def BaseFam : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
      IsCoefFam ε ⟨D, E, hK.gl⟩ (fun ξ : D => baseCoef σ D (ξ : H))

def LabelTrack : Prop :=
  ∀ (n : ℕ) (χ : Fin n → ℂ) (ss : List (Fin n)) (B : ℝ) (j : ℕ), GoodPath χ ss → FarLabels χ (pathEnd χ ss) B →
    ∀ L ∈ moveIter χ {L | IsLabel j L ∧ (deg χ L).re < 0} ss, (deg (pathEnd χ ss) L).re < -B

end CompanionTheory.RgExh.Dec.J
