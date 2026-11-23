import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesUnramifiedPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelEstablishedStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem hodge_cpt_global_nefness : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → 1 ≤ D.p → 1 ≤ D.q → ∀ (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → 2 < p → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ mu : GlobalTheory.CompanionTheory.Ar.Top.Wt (CMType H) (D.p + D.q), GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold D.p p mu → M.NefAt p mu 0 := by
  intro E _ _ _ H D Xo Yl hYl l c hg Y hdom hp1 hq1 S _ M 𝔐 Fl e hRL p hp hp2 hpS hdisc mu hmu hthr
  have hfib := (GlobalTheory.T.global_model_power_free E H D Xo Yl hYl l c hg Y hdom).2 p hp
  obtain ⟨t⟩ := GlobalTheory.T.root_lines_unramified_primes E H D l (Xo l) c Y S M 𝔐 Fl e hRL p hp hpS hdisc hfib
  exact GlobalTheory.T.rootLineDeRhamModel_holds (CMType H) (D.p + D.q) M D.p p E H t hp hp2 hp1 (by omega) mu hmu hthr

end GlobalTheory.CompanionTheory.Ar.Conj
