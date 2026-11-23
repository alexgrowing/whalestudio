import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.GalClose
open GlobalTheory.CuspRep
theorem purity_alt (hRP : GlobalTheory.Published.RegularAlgebraicPurity) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (a : ℕ) (π : D.naut.CG a) (hr : D.naut.ralg π) : ∃ w₀ : ℂ, ∀ τ : D.host.E →+* ℂ,
      D.naut.infG π (τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom) =
        (D.naut.infG π τ).map (w₀ - ·) := by
  have := host_isCMField D.host
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · haveI := P.cg.zero
    exact isEmptyElim π
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨w₀, hw⟩ := (hRP D.host.E a ha1 π₀ hr₀).1
  refine ⟨(w₀ : ℂ), fun τ => ?_⟩
  have hc : τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ :=
    RingHom.ext fun x => GlobalTheory.SplitRowProbe.conj_sqrt D.host τ x
  rw [hc, hinf, hinf, hw]
end GlobalTheory.GalClose
end
end
