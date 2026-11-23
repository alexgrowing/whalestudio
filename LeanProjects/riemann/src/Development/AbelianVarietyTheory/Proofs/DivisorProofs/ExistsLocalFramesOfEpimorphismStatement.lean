import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfEpimorphism
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_frames_of_epimorphism : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (r m : ℕ) (E F : B.X.Modules) (φ : F ⟶ E), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB F m → Epi (B.genRes.map φ) → ∀ x : B.X, ∃ (V : B.X.Opens) (eF : Fin m → Γ(F, V)) (eE : Fin r → Γ(E, V)) (a : Matrix (Fin r) (Fin m) Γ(B.X, V)), x ∈ V ∧ IsAffineOpen V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, φ.app V (eF j) = ∑ k, a k j • eE k) ∧ ∃ J : Fin r → Fin m, (a.submatrix id J).det ≠ 0 := by
  first | exact @GlobalTheory.MixedLocalChains.exists_frames_maximal_minor_ne_zero | exact GlobalTheory.MixedLocalChains.exists_frames_maximal_minor_ne_zero | (intros; apply GlobalTheory.MixedLocalChains.exists_frames_maximal_minor_ne_zero <;> assumption)
