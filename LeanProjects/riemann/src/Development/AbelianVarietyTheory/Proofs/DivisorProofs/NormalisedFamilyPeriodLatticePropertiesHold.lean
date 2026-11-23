import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement

noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem periodLattices : PeriodLattices := by
  intro D X s cc δ B χ cD _hX hok _h1 _h2 hcc hδ _hχ _hdg _hY a b S ha hb hconj hU
  exact ⟨KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, hU, aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

end GlobalTheory.ColNorms
