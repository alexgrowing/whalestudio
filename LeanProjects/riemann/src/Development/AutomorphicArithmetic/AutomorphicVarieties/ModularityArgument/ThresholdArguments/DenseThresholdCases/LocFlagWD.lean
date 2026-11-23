import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FlagWD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → FlagWD := by
  intro hN L Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh ω ψ hψ ⟨M, hM⟩ HT P hD O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d, hJ, -⟩ := hD O Bw hj
  have hc := fun i => (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hN h hw ι a ha (ω i) (hh i) (ψ i) (hψ i)).1 O Bw hj
  obtain ⟨F₁, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj r (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
  refine ⟨d, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · have e := F₁ τ _ _ (hJ τ LL' τ' hτ) fun i => (hc i).2.1 τ LL' τ' hτ
    have e' : (Finset.univ.val.map fun j => hh j τ) = HT τ := by
      rw [e, Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map fun j => hh j τ), Multiset.map_map]
      rfl
    beta_reduce
    rw [e']
    exact hJ τ LL' τ' hτ
  · rw [(F₂ (hN.aut.berger.isPstAt T Bw r (Units.continuous_val.comp hr) d)).2 s]
    exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
end
