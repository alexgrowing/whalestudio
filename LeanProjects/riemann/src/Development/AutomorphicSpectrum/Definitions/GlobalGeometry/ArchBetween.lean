import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptHt (a : K → ℝ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) + ∑ σ : L →+* ℂ, φ fun p => σ (w p))

def lineHt (A : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  ptHt (fun k => (A.a k : ℝ)) (fun z => Real.log (A.h z)) L w

def GenUnit (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y), ∃ val : L, val ≠ 0 ∧ HasVal y a u z val

def VertBound (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (c : ℝ) : Prop :=
  u ≠ 0 ∧ ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ Real.log m ≤ q * c ∧ (m : Ω) * u ^ q ∈ chartLatNm y a q ∧
    (m : Ω) * u⁻¹ ^ q ∈ chartLatNm y (-a) q

def PlaceBound (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (g : MRing ι) (α : ℕ → ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ z ∈ algPts p (mCoordIdeal y), aeval z g ≠ 0 →
    ValLe y a u z (Real.exp (α p) * supMet a z)

def AmpleQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∃ (m l : ℕ) (s : Fin l → Ω), (∀ i, s i ∈ chartLatNm y (fun k => m * a k - 1) 1) ∧
    ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y),
      ∃ (i : Fin l) (val : L), val ≠ 0 ∧ HasVal y (fun k => m * a k - 1) (s i) z val

end Points

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def rootHt (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, M.ι k) → L) : ℝ :=
  ∑ j, M.coef lam s j * lineHt (M.line t j) L w

def joinOf (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) : (Σ k, joinIdx M.ι R.ι k) → M.Ω :=
  joinVec M.y fun p => i (R.y p)

def joinDeg (M R : RootModel Ψ N) (j : Option (Ψ × Fin N)) : M.K ⊕ R.K → ℤ :=
  Sum.elim (M.line 1 j).a (-(R.line 1 j).a)

structure Close (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c : ℝ) : Prop where
  kA : M.kA = R.kA
  unit : ∀ j, GenUnit (joinOf M R i) (joinDeg M R j) (u j)
  vert : ∀ j, VertBound (joinOf M R i) (joinDeg M R j) (u j) c

def ArchBetween (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Wt Ψ N)
    (s lo hi : ℝ) : Prop :=
  ∀ z ∈ ptsOver ℂ (mCoordIdeal (joinOf M R i)), ∀ val : Option (Ψ × Fin N) → ℂ,
    (∀ j, HasVal (joinOf M R i) (joinDeg M R j) (u j) z (val j)) →
      ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (joinInl M.ι R.ι p)) -
        Real.log ((R.line 1 j).h fun p => z (joinInr M.ι R.ι p)) - Real.log ‖val j‖) ∈ Set.Icc lo hi

def HasRef (T : RootTower Ψ N) (R : T.Comp → RootModel Ψ N) : Prop :=
  ∃ (C s₀ : ℝ), 0 < s₀ ∧ ∀ B : ℕ, 2 ≤ B → ∀ c, ∃ (i : (R c).Ω →+* (T.M B c).Ω) (u : Option (Ψ × Fin N) → (T.M B c).Ω),
    Close (T.M B c) (R c) i u (C * Real.log B) ∧ ∀ (mu : Wt Ψ N) (s : ℝ), Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ →
      ArchBetween (T.M B c) (R c) i u (scale s) mu s (-(C * Real.log (1 / s)) - C) C

def RefLower (R : RootModel Ψ N) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    -C ≤ rootHt R 1 0 1 L w ∧ ∀ mu : Wt Ψ N, Dominant mu → ‖mu‖ ≤ 2 →
      -(C * Real.log (2 + C + rootHt R 1 0 1 L w)) - C ≤ rootHt R 1 mu 0 L w

def FlatUnit (R : RootModel Ψ N) : Prop :=
  ∀ τ, ∃ (k : ℕ) (u : R.Ω) (c : ℝ), 0 < k ∧ GenUnit R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u ∧
    VertBound R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u c

def FibreInput {j k : ℕ} (R : RootModel Ψ (j + k)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : L →+* L')
      (E : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L') (A : FlagPair E Ψ j k), A.IsOrthFull ∧
      (∀ τ (i : Fin j), |lineHt (R.x 1 (τ, Fin.castAdd k i)) L w - (A.W τ).grDeg i| ≤ C) ∧
      (∀ τ (i : Fin k), |lineHt (R.x 1 (τ, Fin.natAdd j i)) L w + (A.S τ).grDeg i.rev| ≤ C) ∧
      E.slopeMax ≤ ((C * Real.log (2 + C + max (-E.normDegree ⊤) 0) + C : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar.Ht
