import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtAdelicRootSymbols
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_at_adelic_root_symbols : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ (c : O.s.Comp) (n : ℕ)
    (A : Fin n → (arIn O.s O.Φ O.met.hm).A c),
    (∀ i, ∀ a ∈ (A i : Sym D.host.E →₀ ℤ).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) →
    FlagAt (fun i => adlOf (O.Φ.C c) (O.met.hm c) (A i)) p → ∀ k : ℕ, 1 ≤ k →
    ∀ (y : Rt D.what₂.Tau O.N) (G : MvPolynomial ((arIn O.s O.Φ O.met.hm).A c) ℝ),
    (∀ v ∈ G.vars, ∀ a ∈ (v : Sym D.host.E →₀ ℤ).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) →
      numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        ((∑ i, X (A i) ^ k) * ((X ((arIn O.s O.Φ O.met.hm).root (Function.update (ArIn.ind Sx) p false) R y c) -
          X ((arIn O.s O.Φ O.met.hm).root (Function.update (ArIn.ind Sx) p true) R y c)) * G)) = 0 := by
  first | exact @GlobalTheory.PowerSumVert.powerSum_vert_mul | exact GlobalTheory.PowerSumVert.powerSum_vert_mul | (intros; apply GlobalTheory.PowerSumVert.powerSum_vert_mul <;> assumption)
