import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeCoordinateGenerator
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_coordinate_generator : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (n : ℕ) (L : AddSubgroup (Fin n → Ω)), LocFree R n L → (∀ i, Summand L (annSub Ω n i)) → ∀ (i : Fin n) (u : Ω), u ≠ 0 → (∀ c, c ∈ (L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i) ↔ ∃ a ∈ R, c = a * u) → ∀ t : Ω, (∃ v ∈ dotDual R L, (∀ j, i < j → v j = 0) ∧ v i = t) ↔ ∃ a ∈ R, t = a * u⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | exact GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HhGraded.main <;> assumption)
