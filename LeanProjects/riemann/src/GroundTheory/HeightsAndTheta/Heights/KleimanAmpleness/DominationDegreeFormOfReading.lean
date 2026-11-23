import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OnePt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Lemmas

variable {Ω : Type} [Field Ω]

theorem sameModel_of_charts (R : Type) [CommRing R] [Algebra R Ω] {K K' : Type} {ι : K → Type}
    {ι' : K' → Type} (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (h₁ : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧ chartRingOver R y c = chartRingOver R y' c')
    (h₂ : ∀ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) →
      ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ chartRingOver R y c = chartRingOver R y' c') :
    IndefiniteRowSideFullHecke.Kleiman2.SameModel R y y' := by
  unfold IndefiniteRowSideFullHecke.Kleiman2.SameModel
  ext z
  constructor
  · rintro ⟨c, hc, p, hp, rfl⟩
    obtain ⟨c', hc', heq⟩ := h₁ c hc
    refine ⟨c', hc', ?_⟩
    rw [← heq]
    exact ⟨p, hp, rfl⟩
  · rintro ⟨c', hc', p, hp, rfl⟩
    obtain ⟨c, hc, heq⟩ := h₂ c' hc'
    refine ⟨c, hc, ?_⟩
    rw [heq]
    exact ⟨p, hp, rfl⟩

theorem sameModel_reindex (R : Type) [CommRing R] [Algebra R Ω] {κ : Type} {N : ℕ} (v : κ → Ω)
    (e : κ ≃ Fin (N + 1)) :
    IndefiniteRowSideFullHecke.Kleiman2.SameModel R (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ e.symm)) := by
  have key : ∀ c : Unit → κ, chartRingOver R (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) c =
      chartRingOver R (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ e.symm)) (fun u => e (c u)) := by
    intro c
    unfold chartRingOver
    congr 1
    ext z
    constructor
    · rintro ⟨⟨u, b⟩, rfl⟩
      exact ⟨⟨u, e b⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock]⟩
    · rintro ⟨⟨u, j⟩, rfl⟩
      exact ⟨⟨u, e.symm j⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock]⟩
  apply sameModel_of_charts
  · intro c hc
    exact ⟨fun u => e (c u), fun k => by simpa [IndefiniteRowSideFullHecke.Kleiman2.oneBlock] using hc k, key c⟩
  · intro c' hc'
    refine ⟨fun u => e.symm (c' u), fun k => by simpa [IndefiniteRowSideFullHecke.Kleiman2.oneBlock] using hc' k, ?_⟩
    have h := key (fun u => e.symm (c' u))
    simp only [Equiv.apply_symm_apply] at h
    exact h

variable {S : Type} [CommRing S] [Algebra S Ω] {N N' : ℕ}

end Lemmas

def Domination.GenericIdentity.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [IsDomain S] (F : Type) [Field F] [Algebra S F] (Ω : Type)
    [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω] [IsFractionRing S F]
    (N N' : ℕ) (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω), x' ≠ 0 → Kleiman.IsDomination S x x' →
    IndefiniteRowSideFullHecke.Kleiman2.SameModel F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) →
    ∃ m : S, algebraMap S Ω m ≠ 0 ∧
      (∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ Kleiman.domRing S x x' i,
        algebraMap S Ω m * b ∈ Kleiman.chartRing S x (Kleiman.singleChart hi)) ∧
      ∀ (L : Kleiman.LineBundle S x) (n : ℕ), ∀ z ∈ Kleiman.pullSecs x' (L.pow n),
        algebraMap S Ω m * z ∈ (L.pow n).secs

def Domination.Reading.Statement : Prop :=
  Domination.GenericIdentity.Statement ∧ Kleiman.Domination.Normal.Statement.{0, 0} ∧
    Kleiman.Domination.Conductor.Statement.{0, 0}

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
