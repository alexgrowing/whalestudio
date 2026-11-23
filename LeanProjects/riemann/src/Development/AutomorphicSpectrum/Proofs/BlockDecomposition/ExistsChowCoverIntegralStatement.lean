import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chow_cover_integral : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X], ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens) (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧ O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open | exact GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open | (intros; apply GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open <;> assumption)
