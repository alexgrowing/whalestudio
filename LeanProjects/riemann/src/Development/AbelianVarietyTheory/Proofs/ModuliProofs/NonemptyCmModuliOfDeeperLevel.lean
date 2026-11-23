import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyLevelQuotStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReducedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientUnramifiedDualNumberPointsStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM

theorem moduli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  intro L L2 hT E _ _ _ H D l l₂ hD hl ⟨Xo₂⟩
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_levelQuot_of_level_dvd L L2 hT E H D l l₂ Xo₂ hD hl
  exact ⟨{ X := Q.X, s := Q.s, qproj := Q.qproj, smooth := Q.smooth, univ := Q.univ,
           rep := GlobalTheory.T.levelQuotient_represents_reduced L L2 E H D l l₂ Xo₂ Q hD hl,
           unram := GlobalTheory.T.levelQuotient_unramified_dualNumberPoints L L2 E H D l l₂ Xo₂ Q hD hl }⟩
end GlobalTheory.ZM
