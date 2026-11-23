import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharHomAdditiveShortExact
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_char_hom_additive_short_exact : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (S : ShortComplex T.Modules), S.ShortExact → QCoh.IsFiniteQC S.X₁ → QCoh.IsFiniteQC S.X₂ → QCoh.IsFiniteQC S.X₃ → chi k (homMod E S.X₂) = chi k (homMod E S.X₁) + chi k (homMod E S.X₃) := by
  first | exact @GlobalTheory.HomExact.chi_homMod_shortExact | exact GlobalTheory.HomExact.chi_homMod_shortExact | (intros; apply GlobalTheory.HomExact.chi_homMod_shortExact <;> assumption)
