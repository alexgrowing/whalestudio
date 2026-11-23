import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ENNReal NNReal

namespace PositivityTheory.KB.LocalOverlapAverage

def AvgS : Prop :=
  ∀ (G H Y X : Type) [Group G] [Group H] [MulAction H Y] [MeasurableSpace X] (ρ : G →* H) (k : ℕ)
    (F : (Fin (k + 2) → Y) → ℝ) (P : Measure X) [IsProbabilityMeasure P] (e : X → Y) (y₀ : Y),
    Inv ρ F → dC F = 0 →
    (∀ (h : Fin (k + 2) → H) (b : Fin (k + 2) → Bool),
      Integrable (fun x : Fin (k + 2) → X => F fun j => h j • if b j then e (x j) else y₀)
        (Measure.pi fun _ => P)) →
    ∀ z : Chn G (k + 1), IsCyc z →
      ev ρ F y₀ z = z.sum fun g r =>
        r * ∫ x, F (fun j => ρ (Fin.partialProd g j) • e (x j)) ∂(Measure.pi fun _ => P)

section Simp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def Kset {q : ℕ} (A : Fin (q + 1) → V →L[ℝ] V) (B : Set V) : Set V :=
  {p | ∃ τ : Fin (q + 1) → ℝ, (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1 ∧
    ∃ y : Fin (q + 1) → V, (∀ j, y j ∈ B) ∧ p = ∑ j, τ j • A j (y j)}

def nrm [MeasurableSpace V] (μ : Measure V) (B : Set V) : Measure V := (μ B)⁻¹ • μ.restrict B

end Simp

def SimpBd : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (q : ℕ) (A : Fin (q + 1) → V ≃L[ℝ] V) (B : Set V),
    IsCompact B → ∃ C : ℝ, ∀ ω : Form V q, ContinuousOn ω (Kset (fun j => (A j : V →L[ℝ] V)) B) →
      (∀ (b : Fin (q + 1) → Bool) (y₀ : V), y₀ ∈ B →
        Integrable (fun y : Fin (q + 1) → V => intS ω fun j => A j (if b j then y j else y₀))
          (Measure.pi fun _ => nrm μ B)) ∧
      ENNReal.ofReal (∫ y, |intS ω fun j => A j (y j)| ∂(Measure.pi fun _ => nrm μ B)) ≤
        ENNReal.ofReal C * ∫⁻ p in Kset (fun j => (A j : V →L[ℝ] V)) B, ‖ω p‖₊ ∂μ

def Unfold : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ), 1 ≤ N → ∀ (d : Dom L N) (μ : Measure (HS L N))
    [μ.IsAddHaarMeasure] (K : Set (HS L N)), IsCompact K → K ⊆ Pos L N →
    ∃ (C : ℝ≥0∞) (K' : Set (Sp L N)), C ≠ ⊤ ∧ IsCompact K' ∧
      ∀ ω : Form (HS L N) q, ContinuousOn ω (Pos L N) → (∀ s, FInv ω (scal L N s)) →
        ∫⁻ p in K, ‖ω p‖₊ ∂μ ≤ C * ∫⁻ x in K', ‖fr ω (ofS L N x)‖₊ ∂d.μ

def Discr : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (K : Set (Sp L N)), IsCompact K →
    {γ : Sp L N | γ ∈ latS L N ∧ γ ∈ K}.Finite

def OverlapG : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (D : Set G),
    IsFundamentalDomain Γ D μ → (∀ K : Set G, IsCompact K → {γ : G | γ ∈ Γ ∧ γ ∈ K}.Finite) →
    ∀ K : Set G, IsCompact K → ∃ M : ℕ, ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) →
      ∫⁻ x in K, f x ∂μ ≤ M * ∫⁻ x in D, f x ∂μ

end PositivityTheory.KB.LocalOverlapAverage

end
