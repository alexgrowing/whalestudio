import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTransposeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateCompletionIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWildStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRootsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjPlaceDual

theorem conjPl_symm (D : D7) {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hy, GlobalTheory.SplitPlaceOver.host_conj_eq', GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), LabAll D P.T → ConjDual D := by
  intro hPr hL D P hLab i PI k v w' hc
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  obtain ⟨c, hc1, hc2, hc3⟩ := hγ2 k v w' hc
  have hw'g : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'g, hγ3 k _ (D.naut.plGw_over k v), hγ1 k v]
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩
  have hc3' : ∀ y, γ k w' (c y) = c (D.ntypes.tg k v y) := hc3
  clear hγ1 hγ2 hγ3
  generalize D.naut.plGw k v = w at hs hc hc2 ⊢
  subst hs
  obtain ⟨hsw', -⟩ := GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w' (conjPl_symm D hc)
  subst hsw'
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i PI) s
  obtain ⟨κ, σ', e, hκ, hκc, hσ', he⟩ := GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose D D.R.nV (P.H.av.rep i PI) s σ hσ
  have hloc : ∀ w, D.naut.locV i PI w = D.nbc.locAU (D.nd.j i)
      (P.H.au.cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI)) w := fun w =>
    by rw [D.nbc.embAV_loc, P.H.emb]
  have hA := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI) s σ hσ
  have hA' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i PI) _ σ' hσ'
  rw [← hloc] at hA hA'
  obtain ⟨b, b', hb, hb', hN, hρ⟩ := GlobalTheory.T.conjugate_completion_iso hPr hL D s.w (GlobalTheory.TypeTame.conjSP s).w c hc1 hc2 κ hκ hκc D.R.nV σ σ' e he
  rw [← hA] at hb
  rw [← hA'] at hb'
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.weilDeligneDualTransport_monodromy_dim_wild D _ _ c hc1 hc2 _ _ D.R.nV b b' hb hb' hN hρ
  have h4 := GlobalTheory.T.weilDeligneLabel_transportDual_inverseRoots D k _ _ c hc1 hc2 _ _ D.R.nV b b' hb hb' hN hρ _ _ hc3'
  refine ⟨fun hm => (P.T.mono0 _ _).2 (h1 ((P.T.mono0 _ _).1 hm)), fun ht σ₁ hσ₁ hw₁ => ?_, h4⟩
  rw [P.T.inePol _ _ σ₁ hσ₁, ← P.T.dim]
  refine h3 (fun σ₂ hσ₂ hw₂ => ?_) σ₁ hσ₁ hw₁
  rw [← P.T.inePol _ _ σ₂ hσ₂, P.T.dim]
  exact ht σ₂ hσ₂ hw₂

end GlobalTheory.ConjPlaceDual
