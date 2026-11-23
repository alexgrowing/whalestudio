import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

section Mono

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {S : GridChoice W Set.univ}

theorem charsIn_mono (h : CharsIn G σ) (hσ : Set.range σ ⊆ Set.range σ') : CharsIn G σ' :=
  ⟨fun j w x => hσ (h.mu0 j w x), fun t w x => hσ (h.xi t w x),
    fun i a b w x => hσ (h.chi i a b w x), fun v hv => hσ (h.eta v hv), fun v hv => hσ (h.chiPsi v hv),
    fun v hv => hσ (h.del v hv), fun v hv => hσ (h.del' v hv)⟩

theorem rootCl_mono (h : RootCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : RootCl σ' S :=
  ⟨fun z hz => hσ (h.1 z hz), fun t w hw z hz => hσ (h.2.1 t w hw z hz), fun w hw => hσ (h.2.2 w hw)⟩

theorem phaseCl_mono (h : PhaseCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : PhaseCl σ' S :=
  fun t Φ β hβ w x y e a b => hσ (h t Φ β hβ w x y e a b)

theorem jetCl_mono (h : JetCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : JetCl σ' S :=
  fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hσ ((h t Φ β hβ τ hτ d hd c).1 j a b),
    fun i a b => hσ ((h t Φ β hβ τ hτ d hd c).2 i a b)⟩

theorem lRatios_mono {μ₀ : T} (h : ∀ i j, LRatiosIn G σ μ₀ i j) (hσ : Set.range σ ⊆ Set.range σ') :
    ∀ i j, LRatiosIn G σ' μ₀ i j :=
  fun i j t Λ Λ₀ a b s c d e => hσ (h i j t Λ Λ₀ a b s c d e)

theorem botCl_mono (h : BotCl W σ) (hσ : Set.range σ ⊆ Set.range σ') : BotCl W σ' := by
  intro i j
  obtain ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, H⟩ := h i j
  exact ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, fun t g hg =>
    ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end Mono

theorem range_algebraMap_mono {M M' : IntermediateField ℚ ℂ} (h : M ≤ M') :
    Set.range (algebraMap M ℂ) ⊆ Set.range (algebraMap M' ℂ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, h x.2⟩, rfl⟩

theorem InNF.and {Q Q' : ∀ M : IntermediateField ℚ ℂ, (M →+* ℂ) → Prop}
    (hQ : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q M (algebraMap M ℂ) → Q M' (algebraMap M' ℂ))
    (hQ' : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q' M (algebraMap M ℂ) → Q' M' (algebraMap M' ℂ))
    (h : InNF Q) (h' : InNF Q') : InNF fun M σ => Q M σ ∧ Q' M σ := by
  obtain ⟨M, hM, hq⟩ := h
  obtain ⟨M', hM', hq'⟩ := h'
  exact ⟨M ⊔ M', IntermediateField.finiteDimensional_sup M M', hQ _ _ le_sup_left hq, hQ' _ _ le_sup_right hq'⟩

theorem nfAll_of : NFChars → NFRoot → NFPhase → NFJet → NFRatio → NFBot → NFAll := by
  intro h1 h2 h3 h4 h5 h6
  obtain ⟨CF0, H⟩ := Big.and h1 (Big.and h2 (Big.and h3 (Big.and h4 (Big.and h5 h6))))
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi ha
  have k := InNF.and (fun M M' h q => charsIn_mono q (range_algebraMap_mono h))
    (fun M M' h q => rootCl_mono q (range_algebraMap_mono h)) c1 c2
  have k := InNF.and (fun M M' h q => ⟨charsIn_mono q.1 (range_algebraMap_mono h), rootCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => phaseCl_mono q (range_algebraMap_mono h)) k c3
  have k := InNF.and (fun M M' h q => ⟨⟨charsIn_mono q.1.1 (range_algebraMap_mono h), rootCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      phaseCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => jetCl_mono q (range_algebraMap_mono h)) k c4
  have k := InNF.and (fun M M' h q => ⟨⟨⟨charsIn_mono q.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => lRatios_mono q (range_algebraMap_mono h)) k c5
  have k := InNF.and (fun M M' h q => ⟨⟨⟨⟨charsIn_mono q.1.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.1.2 (range_algebraMap_mono h)⟩, lRatios_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => botCl_mono q (range_algebraMap_mono h)) k c6
  obtain ⟨M, hM, ⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩⟩ := k
  exact ⟨M, hM, ⟨q1, q2, q3, q4, q5, q6⟩⟩

end GlobalTheory.RowEx

end
