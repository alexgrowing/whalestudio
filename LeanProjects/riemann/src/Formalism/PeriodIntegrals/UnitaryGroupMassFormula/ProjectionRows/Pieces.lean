import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.DvProjRowsOfSteps
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

def Hyp (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K) (e : Module.End K A.V) (n : ℕ)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  StarIsConj K ∧ IsProj A e n ∧ IsHermE A e h ∧ IsCMFormE A e h

def LamFG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e → (lamSub A e h U).FG

def GramCS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y →
      (Matrix.of fun i j => h (y i) (y j)).det ≠ 0 ∧
      Real.log |((Algebra.norm ℚ (Matrix.of fun i j => h (y i) (y j)).det : ℚ) : ℝ)| ≤
        2 * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re

def LocalGamma : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y → (∀ i, y i ∈ lamSub A e h U) →
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) →
      ∀ (w : HeightOneSpectrum (𝓞 K)) (k : ℤ), IsValG A e h U w k →
      ∀ w' : HeightOneSpectrum (𝓞 K), IsConjPlK w w' →
        k = -vAdd w (Matrix.of fun i j => h (y i) (y j)).det -
          Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) (lamSub A e h U) -
          Formalism.HermitianLatticesTheory.lidx w'.asIdeal (Submodule.span (𝓞 K) (Set.range y)) (lamSub A e h U)

def ConjPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    ∃ c : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K), Function.Involutive c ∧
      ∀ w, IsConjPlK w (c w) ∧ Ideal.absNorm (c w).asIdeal = Ideal.absNorm w.asIdeal

def NormFinsum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K), x ≠ 0 →
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w x : ℝ) =
      Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ)

def ArchIdentity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) →
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e →
      Submodule.span K (Set.range u) = U →
      LinearIndependent K y → (∀ i, y i ∈ LinearMap.range e) → (∀ i, ∀ x ∈ U, h (y i) x = 0) →
      ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v (Fin.append u z)).det.re -
        ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re +
        ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re =
        Real.log |((Algebra.norm ℚ (Matrix.of fun i j => h (y i) (z j)).det : ℚ) : ℝ)|

def LocalPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) →
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e →
      Submodule.span K (Set.range u) = U →
      (∀ i, Fin.append u z i ∈ cutE A e A.L) →
      LinearIndependent K y → (∀ i, y i ∈ lamSub A e h U) →
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) →
      ∀ w w' : HeightOneSpectrum (𝓞 K), IsConjPlK w w' →
        vAdd w (Matrix.of fun i j => h (y i) (z j)).det +
          Formalism.HermitianLatticesTheory.lidx w'.asIdeal (Submodule.span (𝓞 K) (Set.range y)) (lamSub A e h U) +
          Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range (Fin.append u z))) (cutE A e A.L) -
          Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range u))
            (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) = 0

end PI.DvRows
