import Development.AutomorphicArithmetic.ResidueCharacters.RowThree
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowOn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclusionSplitOfHub

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem rowThreeAt_of_setup_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    RowOnAt L X.ρ (fun l => l = 3 ∧ l ∉ D.host.small) 6000 30000 := by
  rintro i hTw ⟨h3, hs⟩ π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h2 : D.nd.l i ≠ 2 := by omega
  have hq : D.nd.l i ≠ D.host.q := h3 ▸ (three_ne_q D).1
  have hd : D.nd.l i ≠ D.host.d := h3 ▸ (three_ne_q D).2
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k => h3 ▸ three_ne_g D k
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hle : D.nd.l i ≤ D.host.splitBound := by have := S.split; omega
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small hl).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, D.host.cls_splitK_or_small hl hle hq hd,
    fun _ v hv => GlobalTheory.HubLoc.ramIdx_eq_one D.host hl hN v hv, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := D.host.split_small _ hl h2 hle
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (cycAt_of i fun e => absurd e h2) hL (decl_split D i h2 hj) (locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs0 : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hs
  have hsl : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
    unfold RowSmall.sl
    rw [hs0, Nat.factorization_eq_zero_of_not_dvd hN]; rfl
  have hh := h0_le D i dc.col (fun e => absurd e h2) hs0.ge (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P X.ρ S.kill S.sha i hTw hsl π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
end UpperTheory.N
theorem UpperTheory.N.exists_nonneg_threeC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.rowThreeAt_of_setup_alt hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
