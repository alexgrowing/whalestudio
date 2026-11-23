import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.S

theorem not_cover_of_isEmpty (D : D7) (h : IsEmpty D.ntw.Tw) : ¬ NTw.TwCover D.ntw := by
  intro hT
  have h2 : Ideal.span {((2 : ℕ) : 𝓞 ↥D.LL0)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    exact top_primitive (K := ↥D.LL0) 2 one_lt_two (by rw [Ideal.span_singleton_eq_top.mpr hu])
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h2
  have hm : ((2 : ℕ) : 𝓞 ↥D.LL0) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact two_ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hm))
  obtain ⟨i, -⟩ := hT 2 Nat.prime_two ⟨P, hP.isPrime, hne⟩ hm
  exact h.false i

structure TwGap (D : D7) where
  ntw : NTw D.R D.host D.what₂ D.LL0 D.nd
  nexp : NExp D.R D.host D.what₂ D.LL0 D.nd ntw
  nth : NTh D.R D.host D.what₂ D.LL0 D.nd ntw nexp
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E (ntw.l i) →
    LocBridge (ntw.l i) D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (ntw.O0 i)

  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (ntw.l i))
    (x : D.nd.Om), x ∈ D.nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g D.nd, D.what₂.embLL ((nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g
  cover : NTw.TwCover ntw

def withTw (D : D7) (W : TwGap D) : D7 :=
  { D with ntw := W.ntw, nexp := W.nexp, nth := W.nth, ntwbr := W.ntwbr, ntwbr_ind := W.ntwbr_ind, nStage_trivialCharacter_coeff_eq := W.nStage_trivialCharacter_coeff_eq }

theorem galTop (D : D7) (h : D.LL0 = ⊤) : IsGalois ℚ ↥D.LL0 :=
  h ▸ IsGalois.of_algEquiv (IntermediateField.topEquiv (F := ℚ) (E := D.what₂.LL)).symm

theorem ties_withTw (D : D7) (W : TwGap D) (hcd : D.s.cdScale = CD.cdScaleOf D.cd) (hds : dsigTie D)
    (hper : ∀ u μ φ F, D.what₂.perCol u μ φ F = 0) (hB : ∀ u φ F, D.what₂.Bu u φ F = 0)
    (hFT : IsEmpty D.what₂.FT)
    (hgal : IsGalois ℚ ↥D.LL0 := by exact Formalism.BasicNotions.Examples₂.galTop _ rfl) :
    Ties (withTw D W) where
  cdScale_tie := fun n ε P Q e h1 h2 A hA => by
    show ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε) A = D.cd.cd P Q _
    rw [hcd]
    exact CD.cdScaleOf_tie D.cd n ε P Q e h1 h2 A hA
  dsig_tie := hds
  bu_def := by
    intro u φ F
    exact (hB u φ _).trans (hper u _ φ _).symm
  tw_cover := twCoverPair_of (NTw.levelLetterCocycles_of_fact _ W.cover)
  ft_occ := fun σ => hFT.elim σ
  baseField_isGalois := hgal

end Formalism.BasicNotions.Examples₂
