import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqAlgebraMapOfCharpoly
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieGalAssembly

theorem potCrysIffWD (D : D7) : PotCrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_mono0L i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_mono0L i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := GlobalTheory.CrysWD.exists_descent r hr L hL
  obtain ⟨-, h2, h1, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  obtain ⟨K', hK, hc'⟩ := h1.1 hc
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ hc').1
  have h4 := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hK _ (D.locT (D.nd.l i))).2 h3
  refine h2.2 ?_
  unfold IsDR at h4
  unfold LocBridge.IsdRE
  simpa using h4

theorem tieGal_of_jumpsCard (hDR : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (hJ : JumpsCard D.nd D.naut) : Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  ⟨GlobalTheory.CrysWD.crysIffWD D, potCrysIffWD D, hJ, fun i => ⟨GlobalTheory.WeilDeligne.InertiaSplit.decomp_away hDR hL D P i, GlobalTheory.ConjGal.main hDR hL D P i,
    GlobalTheory.T.de_rham_weight_direct_sum hDR hL D P i, GlobalTheory.T.de_rham_weight_twist_character hDR hL D P i⟩⟩

theorem main : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), JumpsCard D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  fun hDR hL D P hJ => tieGal_of_jumpsCard hDR hL D P hJ

end GlobalTheory.TieGalAssembly
