import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.RowDef
import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub
import Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem UpperTheory.N.rowAt_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : Setup L nch HW X C₂) :
    UpperTheory.N.RowAt L X.ρ 6000 30000 := by
  intro i hTw hs h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨by have := hl.two_le; omega, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 :=
    D.host.QS_split _ hl h2 (Nat.dvd_of_mem_primeFactors hs)
  obtain ⟨dc, -, h⟩ := UpperTheory.N.conclusion_split hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun e => absurd e h2) hL (UpperTheory.N.decl_split D i h2 hj) (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs1 : 1 ≤ D.nd.s0 i := by rw [D.nd.restNLevelExponent_of_odd i h2]; exact le_max_left _ _
  have hh := UpperTheory.N.h0_le D i dc.col (fun e => absurd e h2) hs1 (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith

theorem UpperTheory.N.rowC : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ UpperTheory.N.RowC A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    UpperTheory.N.rowAt_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
