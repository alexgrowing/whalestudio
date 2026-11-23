import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeFlagTransitiveLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_even_lattice_flag_transitive_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) → ∀ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → ∀ g : GLoc σ J v, ∃ p : GLoc σ J v, ∃ k ∈ stabLat σ J Λ, g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id ∧ (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Iwasawa.iwasawa_loc | exact GlobalTheory.CompanionTheory.KFin.Iwasawa.iwasawa_loc | (intros; apply GlobalTheory.CompanionTheory.KFin.Iwasawa.iwasawa_loc <;> assumption)
