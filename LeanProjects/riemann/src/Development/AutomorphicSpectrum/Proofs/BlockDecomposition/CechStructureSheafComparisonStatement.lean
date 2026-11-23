import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparison
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_structure_sheaf_comparison : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.cech_OSys_homology_equiv | exact GlobalTheory.CompanionTheory.Hodge.Nerve.cech_OSys_homology_equiv | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.cech_OSys_homology_equiv <;> assumption)
