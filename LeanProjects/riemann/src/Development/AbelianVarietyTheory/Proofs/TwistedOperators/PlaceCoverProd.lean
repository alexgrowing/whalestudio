import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeProductCover

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem lev_of_isConjPl (D : D7) {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') :
    Formalism.IndefR.Lev.IsConjPl P P' := fun c hc =>
  ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) c,
    (h c _ rfl).1 hc, by
      show D.host.conj (c : D.host.E) = star (c : D.host.E)
      rw [star_eq_conj]⟩

theorem place_cover_prod : ∀ (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg),
    (∀ kv, ((plg kv : ↥Pg) : Formalism.L2.DIV.Pl D.host.E) = D.naut.plGw kv.1 kv.2) →
    ∀ PP : Formalism.L2.DIV.Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∈ Pg ∨ ∃ PP' ∈ Pg, IsConjPl PP' PP := by
  intro D Pg plg hplg PP hPP
  have hmul : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← Nat.cast_mul]; exact hPP
  have hk : ∃ k : Fin 2, PP ∈ placesOver D.host.E (D.host.g k) := by
    rcases PP.isPrime.mem_or_mem hmul with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k PP hk
  · left
    rw [hv, ← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  · right
    refine ⟨(plg ⟨k, v⟩ : Formalism.L2.DIV.Pl D.host.E), (plg ⟨k, v⟩).2, ?_⟩
    rw [hplg ⟨k, v⟩]
    exact lev_of_isConjPl D hv

end GlobalTheory.TypeProductCover
