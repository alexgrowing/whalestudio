import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockVectorNotKilledStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterLabelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreenStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualOfLabelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfJointCond
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroRow

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  intro hP hDZ hL D P hRow hLab hCen hGreen hChi
  obtain ⟨S, hS, -, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hP.fin hL D P hRow
  have hLoc : LocDZ hL D := GlobalTheory.DepthZeroAssembly.locDZ_of_split_reg hL D
    (GlobalTheory.T.split_local_of_green hP hDZ hL D P.ty.grp hGreen) (GlobalTheory.T.regularLocal_of_depthZero hP hDZ hL D P.ty.grp hGreen)
  have hConj : ConjDual D := GlobalTheory.T.conj_dual_of_labels hP hL D P hLab
  intro i k v PI
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro ρ f hρ hser hocc hsq hu
  have hw : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_block_vector_not_killed hP hL D P hCen S hS i PI k v hw ρ f ⟨hρ, hser⟩ hocc
  obtain ⟨htame, hχ, u, hu', hlabχ⟩ := GlobalTheory.T.tame_character_label hP hDZ hL D P hChi S hS i k v hw
  obtain ⟨hmono, hlab⟩ := hLoc k v (S i _ hw).mu hχ (u : ZMod (D.host.g k)) ((S i _ hw).rep PI) ρ f htame hlabχ
    ⟨hρ, hser⟩ hsq (hu u hu') ⟨x, hx⟩
  have hrc : rcAt hL D (D.naut.plGw k v) _ ((S i _ hw).rep PI) = P.T.e _ (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [← hS.rc i _ hw]
    exact ((S i _ hw).locV PI).symm
  have hm0 : D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [hrc] at hmono
    exact (P.T.mono0 _ _).2 hmono
  have hl : D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t := by
    rw [P.lab k v, ← hlab]
    unfold labAt
    rw [hrc]

  have hf0 : D.ntypes.eSer k f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hser
    exact GlobalTheory.SerOSys.ZSum.zIdem_ne_zero ρ hρ hser.symm
  have hdegf : f.natDegree = D.R.r := by
    by_contra hne
    exact hf0 (D.ntypes.eSer_zero k f fun h => hne h.2.1)
  have hfne : f ≠ 0 := by
    intro h; apply hf0; exact D.ntypes.eSer_zero k f fun h' => by rw [h] at h'; exact (h'.1.ne_zero rfl)
  have hdeg : (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t).natDegree = D.R.nV := by
    rw [natDegree_mul hfne (pow_ne_zero _ (X_sub_C_ne_zero _)), natDegree_pow, natDegree_X_sub_C, hdegf, mul_one]
    rfl
  refine ⟨u, hu', hm0, hl, fun w' hc => ?_⟩
  obtain ⟨hc1, -, hc3⟩ := hConj i PI k v w' hc
  have hroots : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹) := by
    rw [hc3, hl]
  refine ⟨hc1 hm0, ?_, hroots⟩
  rw [← card_rootsBar, hroots, Multiset.card_map, card_rootsBar, hdeg]

end GlobalTheory.DepthZeroRow
