import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem regAt_minorIJ_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (N : ℕ) (A : Matrix (Fin N) (Fin N) Ω), z ∈ mcPts (mCoordIdeal x) → (∀ a b, RegAt x (mCoordIdeal z) (A a b)) → ∀ I J : Finset (Fin N), RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (Matrix.of fun a b => valAt x (A a b) z) I J := by
  intro K _ ι _ Ω _ x z N A hz hA I J
  let A' : Matrix (Fin N) (Fin N) (GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) :=
    Matrix.of fun a b => ⟨A a b, hA a b⟩
  have hAA : A = A'.map (GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z).subtype := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) : Ω) := by
    rw [hAA, GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.minorIJ_map]
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h1]
    have h2 : valAt x ((minorIJ A' I J : GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) : Ω) z =
        GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regVal x hz (minorIJ A' I J) := rfl
    rw [h2, ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.minorIJ_map]
    congr 1

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
