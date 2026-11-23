import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefPartialSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefIndicatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefCombinationOfPartialIndicatorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

noncomputable section

namespace GlobalTheory.HtNefCore

theorem exists_cover_nefOver : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  intro h2 hH D O hc hf A T H hr c Q l hl hlp
  obtain ⟨V, M, hM, hA⟩ := GlobalTheory.T.adelic_norm_nef_partial_sums h2 hH D O hc hf A T H hr c Q l hl hlp
  refine ⟨V, M, hM, fun n hn => ?_⟩
  have hB := GlobalTheory.T.adelic_norm_nef_indicators h2 hH D O hc hf A T H hr c Q l hl hlp V M hM
  exact GlobalTheory.T.nef_combination_of_partial_indicators V.ar D.what₂.Tau O.N M l (fun τ i hi => by convert hA τ i hi) (fun τ => by convert hB τ using 3) n hn

end GlobalTheory.HtNefCore
