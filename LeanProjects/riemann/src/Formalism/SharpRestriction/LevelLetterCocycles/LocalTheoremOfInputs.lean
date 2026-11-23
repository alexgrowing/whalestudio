import Formalism.SharpRestriction.LevelLetterCocycles.LocalCorollaryOfDeRham
import Formalism.SharpRestriction.LevelLetterCocycles.Realised2Pf
import Development.AutomorphicArithmetic.BlochKatoExtensions.BkExtHolds
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfUTieRec
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfComplMax
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeEveryTheory
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def levBOfSit {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))} {E : EtSit P AI K s LL h W}
    (S : CmpSit P AI K s LL h E) : LevB W where
  levB := S.tie.levB
  mem := S.tie.levB_mem
  supp := S.tie.levB_supp

set_option maxHeartbeats 1000000 in

theorem local_theorem_of_inputs (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F)
    (hP6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hPr2a : Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F)
    (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F)
    (h3 : adm3 D HW F) (h4 : ArchimedeanSignatureMatching D HW F C) (h7 : adm7 D HW F Cm)
    (h8 : adm8 D HW F) (h9a : adm9 D HW F) (h10 : adm10 D HW F) (h14 : adm14 D)
    (hDdR : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) : Conclusion1 D 800 := by
  refine local_theorem_of_cyclotomic_lift D.loc id (fun l _ K LL h => (HW l).W K 1 LL h.2.2)
    (fun l _ K LL h _ h5 hz => ?_) (Formalism.MainNotions.UnusedSlot80.base_change_every_theory D.loc)
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  refine crystalline_lifting_second_form (brHyp2_of_rec (D.loc l) h h5 _ ((HW l).W_s K 1 LL h.2.2)
    (hP5 l K 1 LL h.2.2) (hP6 l K 1 LL h.2.2) (hP9 l K 1 LL h.2.2) (hPr2a l K 1 LL h.2.2)
    (h3.1 l K 1 LL h.2.2) (h4 l K 1 LL h.2.2)
    (h7 l K LL h h5).1 (h9a l K LL h h5) (h10 l K LL h h5) (h14 l K LL) ?_)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨e, he⟩ := hUG l K LL h h5
  refine ⟨e, he, UpperTheory.Prune.bkExt_holds D HW F h9 hFont l K LL h h5 e he, fun hR => ?_⟩
  have hV := valRing_rec (D.loc l) LL
  have hpl := (D.loc l).PD_p K
  have : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  have : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac LL
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) :=
    (mem_maximalIdeal _).2 (not_isUnit_p ((HW l).W K 1 LL h.2.2) hV)
  have hpm' : ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
    have h' := hpm
    rwa [hpl] at h'
  have hp0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have h0' := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h0'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h0'
  have : IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Ln03.Pf.complMax_holds ↥(OL LL) l hpm' hp0 (complete_OL LL)
  obtain ⟨uZ, huZ, hutie⟩ := Formalism.MainNotions.N.Ln03.Pf.uTieRec_holds D HW l K LL h h5
  have hrich : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ finrank ℚ_[l] ↥(K0 K)) := by
    obtain ⟨ζ, hζ⟩ := hz
    exact ⟨ζ, by rw [hpl]; exact hζ⟩
  have h5' : 5 ≤ ((D.loc l).PD K).p := by rw [hpl]; exact h5
  refine realised2_pf (K := ↥K.1) (W := (HW l).W K 1 LL h.2.2) (levBOfSit ((Cm l).C K 1 LL h.2.2)) hR e uZ
    (ιZrec (D.loc l) K LL)
    ?_ ?_ ?_ ?_ ?_ ?_ ((HW l).W_s K 1 LL h.2.2) (hP4 l K 1 LL h.2.2) ?_ ?_ (hP3 l K 1 LL h.2.2)
    (hP9 l K 1 LL h.2.2) (hP5 l K 1 LL h.2.2) ?_ ?_ ?_ hV (unram_of_caseA h) hpm hrich huZ hutie he ?_ h5'
  · exact ((Cm l).C K 1 LL h.2.2).tie.levN_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.cmp_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_φ
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_φ
  · exact (h7 l K LL h h5).2
  · exact h8 l K LL h h5
  · exact hLem3 l K 1 LL h.2.2
  · exact hDdR l K LL h
  · exact (h14 l K LL).1
  · exact Formalism.MainNotions.LiftingTheory.gen_one_crys _

theorem logb_nat_nonneg_sk (p h : ℕ) (hp : 11 ≤ p) : 0 ≤ Real.logb p (h : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · apply Real.logb_nonneg
    · have : (11 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · exact_mod_cast hh

theorem corollary_monotone_in_constant (D : D7) (C C' : ℝ) (h : C ≤ C') (H : Conclusion2 D C) : Conclusion2 D C' := by
  intro l _ K LL n _ emb
  have H' := H l K LL n emb
  intro hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT hb hC
  obtain ⟨mm, k, e1, e2, e3⟩ := H' hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT
    (le_trans (by gcongr) hb) hC
  refine ⟨mm, k, e1, e2, le_trans e3 ?_⟩
  have hp : (11 : ℝ) ≤ ((D.loc l).PD K).p := by exact_mod_cast h11
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h ?_) ?_) ?_) ?_
  · positivity
  · positivity
  · have := logb_nat_nonneg_sk ((D.loc l).PD K).p (hCor b w S η sz) h11
    have h3 : (0 : ℝ) ≤ (((D.loc l).PD K).p : ℝ) - 1 := by linarith
    positivity
  · positivity

theorem corollary_local_exists_constant : ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ),
    Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F → Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F → Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F →
    adm3 D HW F → ArchimedeanSignatureMatching D HW F C → adm7 D HW F Cm → adm8 D HW F → adm9 D HW F →
    adm10 D HW F → adm12 D → adm14 D →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1) →
    Formalism.MainNotions.LocalSituation.adm9 D HW F → Formalism.MainNotions.InvariantsGenerators.LitFont D HW F →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) →
    Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → Conclusion2 D C₂ := by
  obtain ⟨C', h1', h'⟩ := corollary_of_Theorem_E
  refine ⟨max C' (4 * 800), fun D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h12 h14
    hDdR h9 hFont hUG => ?_⟩
  have hp1 := local_theorem_of_inputs D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h14 hDdR h9 hFont hUG
  refine ⟨hp1, fun C₂ h2 => ?_⟩
  refine corollary_monotone_in_constant D _ C₂ h2 ?_
  refine h' D 800 (by norm_num) hp1 h12 ?_
  intro l _ K LL n _ emb T₁ T₂ F h1 h2 hF i A hA' τ hτ a ha
  exact hA' τ hτ a ((h14 l K LL).1 T₁ T₂ F h1 h2 hF τ a ha)

end Formalism.MainNotions.N.Ln03
