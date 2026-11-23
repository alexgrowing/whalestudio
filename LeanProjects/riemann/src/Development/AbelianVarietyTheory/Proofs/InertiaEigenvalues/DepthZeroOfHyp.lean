import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaUnipotentDepthZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfStabilizerTrivial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise

namespace GlobalTheory.DepthZeroType

theorem isSplitPl_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

theorem mem_Ine_of_wild (D : D7) (w : PlE D.host) {σ} (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 w)) :
    σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.HubX.DepthZeroG D := by
  intro hp h1 h2 hL D P hR i w hwS hk Q σ hσ
  obtain ⟨S, hS, -, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hp.fin hL D P hR
  have hw : IsSplitPl D.host w := hk.elim fun k h => isSplitPl_of_over D k w h
  have ht := (GlobalTheory.MuTameQS.main hL D P S hS i w hw (Or.inl hwS)).1
  obtain ⟨v, hv0, hv⟩ := (GlobalTheory.T.tame_block_type_at_split_place hL D P S hS i w hw hk ht).2 Q
  have hfix : v ∈ GlobalTheory.PRep.fixed ((S i w hw).rep Q).π
      (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
    intro h
    have := GlobalTheory.JacBlock.KOne_le_stab ht hv h.2
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  rw [P.T.inePol w _ σ (mem_Ine_of_wild D w hσ), (S i w hw).locV Q, hS.rc]
  exact GlobalTheory.T.inertia_unipotent_depth_zero hp.bz h1 h2 hL D w _ _ ⟨v, hfix, hv0⟩ σ hσ

end GlobalTheory.DepthZeroType
