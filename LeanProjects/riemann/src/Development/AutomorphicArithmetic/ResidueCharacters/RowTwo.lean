import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.RowThreeC
import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub
import Development.AutomorphicArithmetic.ResidueCharacters.TwoDecl
import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem UpperTheory.N.rowTwoAt_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : Setup L nch HW X C₂) :
    UpperTheory.N.RowOnAt L X.ρ (fun l => l = 2) 6000 30000 := by
  intro i hTw h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hs : D.nd.l i ∈ D.host.small := by rw [show D.nd.l i = 2 from h2]; exact UpperTheory.Small.two_mem D.host
  have h4 : 2 ^ 2 ∣ D.host.QS := (pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  obtain ⟨dc, -, h⟩ := UpperTheory.N.conclusion_split hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun _ => (h4.mul_right _).mul_right _) hL (UpperTheory.N.Two.decl_split D i h2)
    (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs2 : 2 ≤ D.nd.s0 i := by
    rw [D.nd.restNLevelExponent_of_two i h2]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization D.host.QS_pos.ne').1 h4
  have hh := UpperTheory.N.h0_le D i dc.col (fun _ => hs2) (by omega) (fun u hu => (dc.cover u).1 (Or.inr hu))
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

theorem UpperTheory.N.rowTwo : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ UpperTheory.N.RowTwoC A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    UpperTheory.N.rowTwoAt_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
