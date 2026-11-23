import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceInfinitesimalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveInducedModuleShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspaceStatement

noncomputable section

open MeasureTheory
open Formalism.REAL (UJ)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open GlobalTheory.Dec (HasInfChar UEquiv)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep IsUnitEquiv)
open GlobalTheory.OpTrace (HasTrace repOp)
open GlobalTheory.RealInd (IsIrrAdm groupRep IndModule)
open GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation (HasWideGaps)

namespace GlobalTheory.SepPseudo

theorem wide_gap {r : ℕ} {lam : Fin r → ℤ} (h : HasWideGaps lam) {i j : Fin r} (hij : i < j) :
    (r : ℤ) ≤ lam i - lam j := by
  have hij' : (i : ℕ) < j := hij
  have hk : (i : ℕ) + 1 < r := by omega
  have h1 := h.2 i ⟨(i : ℕ) + 1, hk⟩ rfl
  have h2 : lam j ≤ lam ⟨(i : ℕ) + 1, hk⟩ := h.1.antitone (by rw [Fin.le_def]; simp; omega)
  linarith

theorem ujMat_surj {n : ℕ} {ε : Fin n → Bool} : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x := fun x hx => by
  obtain ⟨g, hg, -⟩ := GlobalTheory.RealIwasawa.exists_uMat x hx
  exact ⟨g, hg⟩

theorem isIrredOn_of_equiv {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H H' : Type} [NormedAddCommGroup H]
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

theorem isTempered_of_isUnitEquiv {G V W : Type} [Group G] [MeasurableSpace G] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {μ : Measure G}
    {π : G →* (V →L[ℂ] V)} {π' : G →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') (ht : GlobalTheory.Orb.IsTempered μ π) :
    GlobalTheory.Orb.IsTempered μ π' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨v, hv, hi⟩ := ht
  refine ⟨A v, by simpa using hv, fun r hr => ?_⟩
  simpa [← hA, LinearIsometryEquiv.inner_map_map] using hi r hr

theorem pseudoCoeffSeparation (hA : GlobalTheory.Published.HarishChandraAnalyticity) (_hP : GlobalTheory.Published.PseudoCoefficientUpq)
    (hC : GlobalTheory.Published.HarishChandraCharacters) (hL : GlobalTheory.Published.LanglandsClassification) :
    GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation := by
  intro r _ ε lam hlam X _ _ _ D hD μ _ f hf V _ _ _ π hπ c hc hc0
  have hinf : HasInfChar ε (fun a => (lam a : ℂ)) π :=
    GlobalTheory.T.pseudocoefficient_trace_infinitesimal hL hC r ε _ X D hD.1.2.2.1 hD.2 μ f hf V π hπ c hc hc0
  refine ⟨hinf, fun hU => ?_⟩
  obtain ⟨b, W₀, hW₀⟩ := GlobalTheory.RealInd.exists_isMinimalFlag ε
  obtain ⟨⟨I, hI, Z, hZ, hker⟩, -⟩ := hL.2.2.1 r ε b W₀ hW₀ V π hπ
  by_cases ha : 0 < I.a
  · exfalso
    have hsm := (GlobalTheory.T.irreducible_K_stable_finite_subspace r ε V π hU hπ.2.2).2
    have hgen := GlobalTheory.T.infinitesimal_character_factor hL r ε V π hπ hsm _ hinf I hI.2 Z hZ
    obtain ⟨I', ha', hj', hre, hgen'⟩ := GlobalTheory.T.positive_induced_module_shift hL r ε I ha _ hgen
    obtain ⟨i, j, hij, he⟩ := GlobalTheory.T.infinitesimal_character_difference hL r ε I' ha' hj' _ hgen'
    have hb := GlobalTheory.T.unitary_factor_kernel hA hL r ε V π hπ hU I hI.2 Z hZ hker ha
    have hpos : 0 < (I.s ⟨0, ha⟩).re := hI.2.2 _
    have hre' : ((lam i : ℝ) - lam j) = (I.s ⟨0, ha⟩).re := by
      rw [← hre, ← he]; simp
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : ((r : ℤ) : ℝ) ≤ ((lam i - lam j : ℤ) : ℝ) := Int.cast_le.2 (wide_gap hlam h)
      push_cast at h1
      linarith
    · have h1 : ((r : ℤ) : ℝ) ≤ ((lam j - lam i : ℤ) : ℝ) := Int.cast_le.2 (wide_gap hlam h)
      push_cast at h1
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
  · have ha0 : I.a = 0 := by omega
    obtain ⟨hM, U, hUρ⟩ := GlobalTheory.Published.Langlands.equiv_of_zero I ha0
    have ht := I.temp
    rw [show GlobalTheory.RealInd.leviOne ε I.W = ⊤ from hM] at ht
    obtain ⟨hσn, hσi, hσU, hσt⟩ := (GlobalTheory.RealInd.isIrrTempered_top_iff μ).1 ht
    have hAdm := (hL.1 r ε I).1
    have hρn : Nontrivial I.H := U.toLinearEquiv.toEquiv.nontrivial
    have hρU : IsURepOn (UJset ε) I.ρ := ⟨I.isCRepOn, fun g hg v => by
      rw [← U.norm_map, hUρ g hg v, hσU.2.1 g hg, U.norm_map], hAdm.2.1⟩
    have hρ : IsIrrAdm ε I.ρ := ⟨hρn, hAdm, isIrredOn_of_equiv U hUρ hσi⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.unitary_factor_equivalence hA r ε I.H I.ρ V π hρ hρU hπ hU Z hZ
    have hπσ : IsUnitEquiv (ujRep hσU) (ujRep hU) :=
      ⟨(T.trans U).symm, fun g v => by
        have hg : ujMat ε g ∈ UJset ε := g.2
        change (T.trans U).symm (I.σ (ujMat ε g) v) = π (ujMat ε g) ((T.trans U).symm v)
        apply (T.trans U).injective
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.trans_apply, hT _ hg, hUρ _ hg,
          ← LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]⟩
    have hπt : GlobalTheory.Orb.IsTempered μ (ujRep hU) := isTempered_of_isUnitEquiv hπσ hσt
    haveI := hπ.1
    have hc' : HasTrace (repOp (ujRep hU) μ f) c := hc
    have hπD : IsUnitEquiv (ujRep hU) (ujRep hD.1.2.2.1) := by
      by_contra hne
      have h0 := hf.trace_other V (ujRep hU)
        (GlobalTheory.Orb.isUnitaryRep_repVia hU (fun g => g.2) GlobalTheory.HCChar.continuous_ujMat)
        (GlobalTheory.Orb.isTopIrreducible_repVia hU (fun g => g.2) ujMat_surj hπ.2.2) hπt hne
      exact hc0 (hc'.2.symm.trans h0.2)
    refine ⟨?_, ?_⟩
    · obtain ⟨A, hA'⟩ := hπD
      refine ⟨A, fun g hg v => ?_⟩
      obtain ⟨g', rfl⟩ := ujMat_surj g hg
      exact hA' g' v
    · have h1 := hπD.symm.hasTrace hf.trace_self
      exact hc'.2.symm.trans h1.2

end GlobalTheory.SepPseudo
