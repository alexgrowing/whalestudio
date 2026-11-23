import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionField
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_finrank_fraction_field : ∀ (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T),
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = m := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | exact GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis <;> assumption)
