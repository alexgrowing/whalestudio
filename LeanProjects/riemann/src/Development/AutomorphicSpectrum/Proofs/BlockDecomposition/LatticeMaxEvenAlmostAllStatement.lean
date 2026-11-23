import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeMaxEvenAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_max_even_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.AE.exists_lattice_maxEven_adapted | exact GlobalTheory.CompanionTheory.KFin.AE.exists_lattice_maxEven_adapted | (intros; apply GlobalTheory.CompanionTheory.KFin.AE.exists_lattice_maxEven_adapted <;> assumption)
