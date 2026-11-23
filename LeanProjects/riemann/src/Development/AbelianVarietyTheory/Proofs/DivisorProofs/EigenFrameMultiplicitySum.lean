import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualEigOfHasDual
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory.MetFam

theorem sum_mult_eq_relDim : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left), IsGrpPullback Q.A s.T.Z.t.G b θ → ∀ (σ' : κ.c.F →+* ℂ) (y₀ : Sp ℂ ⟶ T), EigFrame s.T.Z σ' (y₀ ≫ b) → ∑ τ : D.host.E →+* ℂ, S.Dw.mult τ = Q.g := by
  intro D A N j S κ s T b Q θ hθ σ' y₀ _
  have : Nonempty T := ⟨y₀ (IsLocalRing.closedPoint ℂ)⟩
  have := Q.smoothDim
  have := Q.isAb.proper
  have := s.T.Z.t.semi.smooth
  have := s.T.Z.t.semi.separated
  exact (LieVB.isVB_omega_of_isGrpPullback hθ (GlobalTheory.DRBaseEx.isVB_omega s.T.Z)).rank_unique (LieVB.isVB_omega Q.A Q.g)

end GlobalTheory.MetFam
