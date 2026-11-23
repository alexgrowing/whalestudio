import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowSameCosetScalarCorankOneStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGen

theorem genFam : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  intro D X Y u u' hsym htr
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t ∈ gCls Y u u' t := by
    intro t ht
    obtain ⟨h1, h2⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t (hG t ht) rfl rfl
    exact ⟨ht, rfl, h1, h2⟩

  have hrow : ∀ t t' : TauC Y u u', t' ∈ gCls Y u u' t → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t :=
    fun t t' h => h.2.1

  have hsub : ∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' →
      gCls Y u u' t' ⊆ gCls Y u u' t := by
    intro t ht t' ht' hr hs hc x hx
    obtain ⟨hxg, hxr, hxs, hxc⟩ := hx
    obtain ⟨h1, h2⟩ := htr t ht t' ht' x hxg hr hxr.symm hs hc hxs hxc
    exact ⟨hxg, hxr.trans hr.symm, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      obtain ⟨hs, hc⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t' (hG t ht) hr hn
      obtain ⟨hs', hc'⟩ := hsym t ht t' ht' hr hs hc
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs' hc') (hsub t ht t' ht' hr hs hc)
  · intro t ht t' ht' he
    have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.SnFamGen
