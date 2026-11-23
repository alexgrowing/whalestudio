import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality

instance instLCM (N : ℕ) : LocallyCompactSpace (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → ℂ))

instance instSCM (N : ℕ) : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))

instance instLCSL (N : ℕ) : LocallyCompactSpace (SpecialLinearGroup (Fin N) ℂ) :=
  haveI : LocallyCompactSpace {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1} :=
    (isClosed_eq (continuous_id.matrix_det) continuous_const).locallyCompactSpace
  inferInstanceAs (LocallyCompactSpace {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1})

instance instSCSL (N : ℕ) : SecondCountableTopology (SpecialLinearGroup (Fin N) ℂ) :=
  haveI : SecondCountableTopology {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1} :=
    TopologicalSpace.Subtype.secondCountableTopology _
  inferInstanceAs (SecondCountableTopology {A : Matrix (Fin N) (Fin N) ℂ | A.det = 1})

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

example : LocallyCompactSpace (Sp L N) := inferInstance
example : SecondCountableTopology (Sp L N) := inferInstance
example : IsTopologicalGroup (Sp L N) := inferInstance
example : T2Space (Sp L N) := inferInstance

variable {L N} in

abbrev mt (x : Sp L N) (w : InfinitePlace L) : Matrix (Fin N) (Fin N) ℂ :=
  ((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)

def KS : Set (Sp L N) := {k | ∀ w, mt k w ∈ unitaryGroup (Fin N) ℂ}

def Om (M : ℝ) : Set (Sp L N) :=
  {p | (∀ w, (mt p w).BlockTriangular id) ∧ (∀ w i j, ‖mt p w i j‖ ≤ M) ∧ (∀ w i, M⁻¹ ≤ ‖mt p w i i‖) ∧
    ∀ i, ∏ w, ‖mt p w i i‖ = 1}

def dg (s : Fin N → ℝ) (hs : ∑ i, s i = 0) : Sp L N := fun _ =>
  ⟨diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ), by
    rw [det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, hs, Real.exp_zero, Complex.ofReal_one]⟩

variable {N} in

def W (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then |s i - s j| else 0

def Sieg (M T : ℝ) : Set (Sp L N) :=
  {x | ∃ p ∈ Om L N M, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T) ∧
    ∃ k ∈ KS L N, x = p * dg L N s hs * k}

variable {L N} in

def IsRatS (c : Sp L N) : Prop :=
  ∃ (g : GL (Fin N) L) (z : InfinitePlace L → ℂ), ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding

end PositivityTheory.KB.MomentRationality

namespace PositivityTheory.KB

open MomentRationality

def SDisc : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), DiscreteTopology (latS L N) ∧ Countable (latS L N)

def SHtB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N → ∀ c : Sp L N, IsRatS c →
    ∀ M : ℝ, ∃ C : ℝ, ∀ p ∈ Om L N M, ∀ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), ∀ k ∈ KS L N,
      ht (ofS L N (c * (p * dg L N s hs * k))) ≤ C * Real.exp (2 * W s)

def SIntB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 2 ≤ N →
    ∀ (μ : Measure (Sp L N)) [μ.IsHaarMeasure] (M T B : ℝ), B < 2 * ((N : ℝ) - 1) →
      ∀ (C : ℝ≥0∞), C ≠ ⊤ → ∀ f : Sp L N → ℝ≥0∞, (∀ p ∈ Om L N M, ∀ (s : Fin N → ℝ) (hs : ∑ i, s i = 0),
        (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T) → ∀ k ∈ KS L N,
          f (p * dg L N s hs * k) ≤ C * ENNReal.ofReal (Real.exp (B * W s))) →
        ∫⁻ x in Sieg L N M T, f x ∂μ < ⊤

def SRedGL : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N →
    ∃ (R : Finset (GL (Fin N) L)) (M t : ℝ), 0 < M ∧ 0 < t ∧ ∀ x : Gp L N, ∃ δ : Gm L N, ∃ g ∈ R,
      ∃ r : Fin N → ℝ, (∀ i, 0 < r i) ∧ (∀ i j : Fin N, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧
        ∀ w, ∃ b : Matrix (Fin N) (Fin N) ℂ, b.BlockTriangular id ∧ (∀ i j, ‖b i j‖ ≤ M) ∧ (∀ i, M⁻¹ ≤ ‖b i i‖) ∧
          ∃ k ∈ unitaryGroup (Fin N) ℂ,
            (((emb L N δ * x) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
              (g : Matrix (Fin N) (Fin N) L).map w.embedding * b * diagonal (fun i => ((r i : ℝ) : ℂ)) * k

def SRed : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N →
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Sp L N) (M T : ℝ), (∀ j, IsRatS (c j)) ∧
      ∀ x : Sp L N, ∃ γ ∈ latS L N, ∃ j, (c j)⁻¹ * (γ * x) ∈ Sieg L N M T

end PositivityTheory.KB

end
