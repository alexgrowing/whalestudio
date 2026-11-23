import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefIndicators
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_norm_nef_indicators : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l := by
  first | exact @GlobalTheory.DetHT.nefOver_det | exact GlobalTheory.DetHT.nefOver_det | (intros; apply GlobalTheory.DetHT.nefOver_det <;> assumption)
