import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTower
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_tower_alt : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | exact GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | (intros; apply GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower <;> assumption)
