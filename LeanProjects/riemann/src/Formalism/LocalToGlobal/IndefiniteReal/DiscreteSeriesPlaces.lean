import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Matrix

namespace Formalism.IndefR.DiscreteSeriesPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

structure PlaceDat (V : HSp D) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) where
  lam : Fin V.rank → ℝ
  ε : Fin V.rank → Bool
  fr : Matrix (Fin V.rank) (Fin V.rank) ℂ
  enum : IsEnum (S τ) lam ε
  hc : Formalism.QuantumDeterminants.IsHCParam lam
  h : ℝ
  gap : Formalism.QuantumDeterminants.GapAtLeast ε lam h
  big : (ReciprocityTheory.ChartRestriction.DS.pOf ε = 0 ∨ ReciprocityTheory.ChartRestriction.DS.qOf ε = 0) ∨
    max (2 * (V.rank : ℝ)) (8 * (V.rank : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) < h
  fr_unit : IsUnit fr
  fr_gram : frᴴ * Formalism.REAL.Jm ε * fr = gramAt D V τ

theorem dsModel_nonempty (P : ∀ τ, PlaceDat V S τ) : Nonempty (DSModel V S) := by
  classical
  have hex : ∀ τ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS (P τ).ε (P τ).lam σ := fun τ =>
    ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap V.rank (P τ).ε (P τ).lam (P τ).hc (P τ).h (P τ).gap (P τ).big
  choose H nH iH σ hσ using hex
  exact ⟨@DSModel.mk D V S H nH iH σ (fun τ => (P τ).lam) (fun τ => (P τ).ε) (fun τ => (P τ).fr)
    (fun τ => (P τ).enum) hσ (fun τ => (P τ).fr_unit) (fun τ => (P τ).fr_gram)⟩

end Formalism.IndefR.DiscreteSeriesPlaces

end
