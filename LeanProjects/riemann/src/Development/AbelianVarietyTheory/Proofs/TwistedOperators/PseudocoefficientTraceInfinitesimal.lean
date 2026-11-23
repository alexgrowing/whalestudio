import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceVanishesStatement

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep IsUnitEquiv)
open scoped InnerProductSpace

namespace GlobalTheory.TraceInfChar

theorem ujMat_onto {n : ℕ} {ε : Fin n → Bool} : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x := fun x hx => by
  obtain ⟨g, hg, -⟩ := GlobalTheory.RealIwasawa.exists_uMat x hx
  exact ⟨g, hg⟩

theorem isIrredOn_of_isom {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H H' : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ g ∈ G, ∀ v, U (ρ g v) = σ g (U v)) (h : IsIrredOn G σ) : IsIrredOn G ρ := by
  intro S hS hst
  let e := U.toLinearEquiv
  have hS' : IsClosed ((S.map (e : H →ₗ[ℂ] H') : Submodule ℂ H') : Set H') := by
    rw [Submodule.map_coe]
    exact U.toHomeomorph.isClosedMap _ hS
  rcases h _ hS' (fun g hg w hw => by
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨ρ g v, hst g hg v hv, hU g hg v⟩) with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : e v ∈ S.map (e : H →ₗ[ℂ] H') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := this
    rwa [e.injective hwe] at hw

theorem isTempered_of_unitEquiv {G V W : Type} [Group G] [MeasurableSpace G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {μ : Measure G}
    {π : G →* (V →L[ℂ] V)} {π' : G →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') (ht : GlobalTheory.Orb.IsTempered μ π) :
    GlobalTheory.Orb.IsTempered μ π' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨v, hv, hi⟩ := ht
  refine ⟨A v, by simpa using hv, fun r hr => ?_⟩
  simpa [← hA, LinearIsometryEquiv.inner_map_map] using hi r hr

theorem hasInfChar_of_trace_ne_zero : GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.HarishChandraCharacters →
    ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
      [CompleteSpace X] (δ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hδ : IsURepOn (UJset ε) δ),
      HasInfChar ε χ δ → ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ),
      IsPseudoCoeff (ujMat ε) μ (ujRep hδ) f → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 → HasInfChar ε χ π := by
  intro hL hC n ε χ X _ _ _ δ hδ hχ μ _ f hf V _ _ _ π hπ c hc hc0
  obtain ⟨b, W₀, hW₀⟩ := exists_isMinimalFlag ε
  obtain ⟨N, I, m, hstd, -, -, -, hinf, htr⟩ := hL.2.2.2.2.1 n ε b W₀ hW₀ V π hπ
  obtain ⟨-, hsum⟩ := htr μ f hf.mem
  have hcs : c = ∑ i, (m i : ℂ) * trace (repOp (I i).rep μ f) := hc.2.symm.trans hsum.2
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hcs ▸ hc0)
  have htr0 : trace (repOp (I i).rep μ f) ≠ 0 := right_ne_zero_of_mul hi
  refine (hinf i χ).1 ?_
  by_cases ha : (I i).a = 0
  · obtain ⟨hM, U, hUρ⟩ := GlobalTheory.Published.Langlands.equiv_of_zero (I i) ha
    have ht := (I i).temp
    rw [show leviOne ε (I i).W = ⊤ from hM] at ht
    obtain ⟨hσn, hσi, hσU, hσt⟩ := (isIrrTempered_top_iff μ).1 ht
    haveI := hσn
    have hAdm := (hL.1 n ε (I i)).1
    haveI hρn : Nontrivial (I i).H := U.toLinearEquiv.toEquiv.nontrivial
    have hρU : IsURepOn (UJset ε) (I i).ρ := ⟨(I i).isCRepOn, fun g hg v => by
      rw [← U.norm_map, hUρ g hg v, hσU.2.1 g hg, U.norm_map], hAdm.2.1⟩
    have hρi : IsIrredOn (UJset ε) (I i).ρ := isIrredOn_of_isom U hUρ hσi
    have hσρ : IsUnitEquiv (ujRep hσU) (ujRep hρU) :=
      ⟨U.symm, fun g v => by
        have hg : ujMat ε g ∈ UJset ε := g.2
        change U.symm ((I i).σ (ujMat ε g) v) = (I i).ρ (ujMat ε g) (U.symm v)
        apply U.injective
        rw [LinearIsometryEquiv.apply_symm_apply, hUρ _ hg, LinearIsometryEquiv.apply_symm_apply]⟩
    have hρt : GlobalTheory.Orb.IsTempered μ (ujRep hρU) := isTempered_of_unitEquiv hσρ hσt
    have hrep : (I i).rep = ujRep hρU := rfl
    have hρδ : IsUnitEquiv (ujRep hρU) (ujRep hδ) := by
      by_contra hne
      have h0 := hf.trace_other (I i).H (ujRep hρU)
        (GlobalTheory.Orb.isUnitaryRep_repVia hρU (fun g => g.2) GlobalTheory.HCChar.continuous_ujMat)
        (GlobalTheory.Orb.isTopIrreducible_repVia hρU (fun g => g.2) ujMat_onto hρi) hρt hne
      exact htr0 (hrep ▸ h0.2)
    obtain ⟨A, hA⟩ := hρδ
    refine GlobalTheory.ClassificationConsequences.hasInfChar_of_uEquiv ⟨A, fun g hg v => ?_⟩ hχ
    obtain ⟨g', rfl⟩ := ujMat_onto g hg
    exact hA g' v
  · exact absurd (GlobalTheory.T.pseudocoefficient_trace_vanishes hC n ε μ X (ujRep hδ) f hf (I i) ha).2 htr0

end GlobalTheory.TraceInfChar

end
