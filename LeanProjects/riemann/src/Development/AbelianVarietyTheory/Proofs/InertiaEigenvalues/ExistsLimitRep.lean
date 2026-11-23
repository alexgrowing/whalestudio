import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfContinuousTrace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendOfLocallyCauchy
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyApproxOfDenseRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPseudoCharacterOfApproximatedByTracesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatedTraceSystemLocallyCauchyStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem exists_limit_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∃ r : Γ →* GL (Fin a) (PadicAlgCl l), Continuous r ∧ IsSSRep r ∧ (∀ j, trc r (x j) = θ j) ∧ PolyApprox (trc r) (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx θ L hL hθL C hC hA
  have hU := GlobalTheory.T.approximatedTraceSystem_locally_cauchy l Γ a J x θ C hC hA
  obtain ⟨T, hTc, hTx⟩ := GlobalTheory.Cong.extend_of_locallyCauchy l Γ J x hx θ L hL hθL hU
  have hA' : PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) := by
    have : (fun j => T (x j)) = θ := funext hTx
    rw [this]; exact hA
  have hT : PolyApprox T (trc '' C) := GlobalTheory.Cong.polyApprox_of_denseRange l Γ a J x hx T hTc C hC hA'
  have hP : IsPsChar a T := GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces l Γ a T C hT
  obtain ⟨r, hr, htr⟩ := GlobalTheory.PsChar.exists_ssRep Γ (PadicAlgCl l) a T hP
  have htrc : trc r = T := funext fun g => htr g
  refine ⟨r, ?_, hr, fun j => by rw [htrc]; exact hTx j, by rw [htrc]; exact hT⟩
  refine GlobalTheory.SSCont.continuous_of_continuous_trace Γ (PadicAlgCl l) a r hr ?_
  have : (fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)).trace) = T := htrc
  rw [this]; exact hTc

end GlobalTheory.Cong
