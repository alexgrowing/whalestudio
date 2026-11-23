import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep repVia CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open GlobalTheory.DSSU (SUJ SUset IsParS IsHCS)
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.SUChar

variable {n : ℕ}

def suMat (ε : Fin n → Bool) : SUJ ε →* Matrix (Fin n) (Fin n) ℂ := (ujMat ε).comp (SUJ ε).subtype

theorem suMat_mem (ε : Fin n → Bool) (g : SUJ ε) : suMat ε g ∈ SUset ε := ⟨g.1.2, g.2⟩

def suRep {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)} (h : IsURepOn (SUset ε) ρ) : SUJ ε →* (X →L[ℂ] X) :=
  repVia h (suMat ε) (suMat_mem ε)

def suTorusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) : SUJ ε :=
  ⟨torusPt ε θ, by
    change (ujMat ε (torusPt ε θ)).det = 1
    rw [ujMat_torusPt, det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, hθ]
    simp⟩

theorem suMat_suTorusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) :
    suMat ε (suTorusPt ε θ hθ) = diagonal fun a => Complex.exp (θ a * Complex.I) := rfl

theorem isInducing_suMat (ε : Fin n → Bool) : Topology.IsInducing (GlobalTheory.Orb.matCoord (suMat ε)) :=
  (isInducing_matCoord (ε := ε)).comp Topology.IsInducing.subtypeVal

def chamberDenom (lam θ : Fin n → ℝ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.univ.filter (fun b => lam b < lam a), (Complex.exp (((θ a - θ b) / 2 : ℝ) * Complex.I) -
    Complex.exp ((-((θ a - θ b) / 2) : ℝ) * Complex.I))

def chamberChar (ε : Fin n → Bool) (lam θ : Fin n → ℝ) : ℂ :=
  (-1) ^ halfDim ε * (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * wtVal (lam ∘ w.symm) θ) / chamberDenom lam θ

theorem chamberDenom_of_strictAnti {lam : Fin n → ℝ} (h : StrictAnti lam) (θ : Fin n → ℝ) :
    chamberDenom lam θ = weylDenom θ := by
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr ?_ fun _ _ => rfl
  ext b
  simp [h.lt_iff_gt]

theorem chamberChar_of_strictAnti (ε : Fin n → Bool) {lam : Fin n → ℝ} (h : StrictAnti lam) (θ : Fin n → ℝ) :
    chamberChar ε lam θ = dsChar ε lam θ := by
  rw [chamberChar, chamberDenom_of_strictAnti h, dsChar]

end GlobalTheory.SUChar

namespace GlobalTheory.Published

open GlobalTheory.SUChar

def DiscreteSeriesCharacterSU : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (SUJ ε)) [μ.IsHaarMeasure] (lam : Fin n → ℝ), IsParS lam →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsHCS ε lam σ) (Θ : SUJ ε → ℂ),
      IsCharFn (suMat ε) μ (suRep h.1.2.2.1) Θ ∧
        ∀ (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0), IsRegSS (suMat ε (suTorusPt ε θ hθ)) →
          Θ (suTorusPt ε θ hθ) = chamberChar ε lam θ

def DiscreteSeriesCharacterOfParameter : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsSqIntIrr ε σ),
      (∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
      (∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
        (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
      ∃ Θ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ ∧
        ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

end GlobalTheory.Published

end
