import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverAntitoneComb
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_over_antitone_comb : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (L x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → ∀ l ∈ Q, l.Prime → NefOver (ArInt.comb L fun x => -n x.1 x.2) l := by
  first | exact @GlobalTheory.HtNef.nefOver_comb_root | exact GlobalTheory.HtNef.nefOver_comb_root | (intros; apply GlobalTheory.HtNef.nefOver_comb_root <;> assumption)
