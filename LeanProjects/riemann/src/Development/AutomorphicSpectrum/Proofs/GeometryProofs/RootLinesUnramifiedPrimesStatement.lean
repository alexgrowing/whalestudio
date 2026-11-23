import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesUnramifiedPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_lines_unramified_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z) → Nonempty (DRTie M D.p p H) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt | exact GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt <;> assumption)
