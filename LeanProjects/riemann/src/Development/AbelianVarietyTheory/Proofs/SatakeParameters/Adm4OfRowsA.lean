import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrueReadingWithLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameRamifiedTypeAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProductStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProductStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypesAtPin

theorem not_over_g_of_mem_Q (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ D.nd.Q i)
    (k : Fin 2) : w ∉ placesOver D.host.E (D.host.g k) := by
  intro hk
  have hS : w ∈ D.nd.S i := (D.nd.S_def i w).2 ⟨by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk), D.nd.SQ_l i w (Or.inr hw)⟩
  exact Finset.disjoint_left.1 (D.nd.SQ_disj i) hS hw

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.NRows.RowsA D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro pr hL D P hrow rA
  obtain ⟨S, hTrue, hLaws, hSupp⟩ := GlobalTheory.T.exists_true_reading_with_laws pr.fin hL D P hrow
  have hTS : TameSplitAll D.host.E := fun w => GlobalTheory.T.tameParahoricRep_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hBS : BlockSplitAll D.host.E := fun w => GlobalTheory.T.blockTypeVector_irreducible_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hchi : ChiIne D.nd D.naut := GlobalTheory.SplitRead.chiIne_main D rA.tie0 rA.a2 rA.a5
    (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr)
  have hTT : ∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) →
      TypeTame S i w hw := by
    intro i w hw h
    have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
      rcases h with hQ | ⟨-, hg⟩
      · exact not_over_g_of_mem_Q D i w hQ
      · exact hg
    have hSQ : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i := by
      rcases h with hQ | ⟨hS, -⟩
      · exact Or.inr hQ
      · exact Or.inl hS
    have ht := GlobalTheory.MuTameQS.main hL D P S hTrue i w hw hSQ
    exact GlobalTheory.T.tame_ramified_type_at_place hL D P S hTrue i w hw hng ht.1 (ht.2 hng)
  have hTB : ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw := by
    intro i w hw hSQ
    have ht := GlobalTheory.MuTameQS.main hL D P S hTrue i w hw hSQ
    by_cases hg : ∃ k, w ∈ placesOver D.host.E (D.host.g k)
    · exact GlobalTheory.T.tame_block_type_at_split_place hL D P S hTrue i w hw hg ht.1
    · have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := fun k hk => hg ⟨k, hk⟩
      have hT : TypeTame S i w hw := hTT i w hw (by
        rcases hSQ with hS | hQ
        · exact Or.inr ⟨hS, hng⟩
        · exact Or.inl hQ)
      refine ⟨hT.1, fun Q => ?_⟩
      obtain ⟨v, hv0, hv⟩ := hT.2.2 Q
      exact ⟨v, hv0, fun h hK h1 _ u hu => hv h hK h1 u hu⟩
  exact GlobalTheory.InertialTypes.main D P.T S hTS hBS hLaws hSupp hchi hTT hTB

end GlobalTheory.TypesAtPin
