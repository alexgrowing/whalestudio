import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalResidueTensorInjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_quotient_module_surjection : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.latQuot_free) | (exact GlobalTheory.UPel.HT.EtLev.latQuot_free) | (intros; apply GlobalTheory.UPel.HT.EtLev.latQuot_free <;> assumption)
