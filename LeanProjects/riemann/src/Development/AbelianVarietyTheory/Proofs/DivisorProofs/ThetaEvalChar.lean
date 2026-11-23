import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogPeriod

theorem theta_eval_char : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ (t : G.Tate) (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → (∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N) → ∀ E : MvPowerSeries (Fin d) F.B →ₐ[F.B] F.B, IsEval p z E → F.θ (E g) = zeta ε n ^ GlobalTheory.PDiv.digit n (epsPairing hε G t χ) := by
  intro p _ O _ _ _ _ ε hε F G d c χ g hg t n z hz hnil E hE
  haveI := F.frame.complete
  let Ev : MvPowerSeries (Fin d) O →ₐ[O] O := (t.pt n).comp (c.ev n)
  have hEv : IsEval p (fun i => F.θ (z i)) Ev := by
    refine ⟨fun i => ?_, fun m => ?_⟩
    · change t.pt n (c.ev n (X i)) = F.θ (z i)
      rw [(c.isEval n).1 i, hz]
    · obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun g hg => ?_⟩
      obtain ⟨w, hw⟩ := hN g hg
      refine ⟨t.pt n w, ?_⟩
      change t.pt n (c.ev n g) = _
      rw [hw, map_mul, map_pow, map_natCast]
  have h1 : F.θ (E g) = Ev (map F.θ g) :=
    ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p F.B F.B (Fin d) z hnil).2 E hE).2.2 O O F.θ F.θ Ev (fun _ => rfl) hEv g
  have h2 : Ev (map F.θ g) = t.pt n (charElem χ n) := by
    change t.pt n (c.ev n (map F.θ g)) = _
    rw [hg n]
  rw [h1, h2, ← GlobalTheory.PDivGroup.muRoot_pairing, ← GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing_smul hε,
    GlobalTheory.PDivGroup.muRoot_smul]
  unfold epsTate
  rw [GlobalTheory.PDivGroup.muRoot_muTate]

end GlobalTheory.QLogPeriod
