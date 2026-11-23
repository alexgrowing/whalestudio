import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleConsecutiveVeryAmple
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_consecutive_very_ample : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∃ d : ℕ, 1 ≤ d ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw L (d : ℤ))) (m' : ℕ) (s' : Fin (m' + 1) → LB.Sec (pw L ((d + 1 : ℕ) : ℤ))), VeryAmpleBy X.hom (pw L (d : ℤ)) s ∧ VeryAmpleBy X.hom (pw L ((d + 1 : ℕ) : ℤ)) s' := by
  first | exact @GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple | exact GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple | (intros; apply GlobalTheory.CompanionTheory.ConsecAmple.exists_consecutive_veryAmple <;> assumption)
