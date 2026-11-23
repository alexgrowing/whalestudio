import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_ring : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc | exact GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc | (intros; apply GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc <;> assumption)
