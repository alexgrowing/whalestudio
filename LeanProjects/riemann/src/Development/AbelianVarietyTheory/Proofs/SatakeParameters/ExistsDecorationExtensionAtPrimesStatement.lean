import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDecorationExtensionAtPrimes
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decoration_extension_at_primes : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet E n ST ∅) (f : SG → (Sp E n ≃ₗ[E] Sp E n)), (∀ (w : SG) (x : Sp E n), f w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) → ∃ d' : DecoSet E n ST SG, d'.1.N = d.1.N ∧ d'.1.f = d.1.f ∧ ∀ w : SG, ∀ x ∈ stdAt E n w.1, d'.1.be w (f w x) = redV w.1 x := by
  first | exact @GlobalTheory.FrameDeco.exists_deco_of_frames | exact GlobalTheory.FrameDeco.exists_deco_of_frames | (intros; apply GlobalTheory.FrameDeco.exists_deco_of_frames <;> assumption)
