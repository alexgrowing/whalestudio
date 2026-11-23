import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOnUnion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsExphOfIsExphOnUniv
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg

open Set

theorem exists_isExph : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (a : ChartForm Y.str σ Y.dim),
    IsKaehlerForm (Y.an σ) a → ∃ E : ChartMap Y.str σ Y.dim, IsExph a E := by
  intro F _ _ Y σ a ha
  haveI : T2Space (CxPts Y.str σ) := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  haveI : CompactSpace (CxPts Y.str σ) := CxPts.compactSpace σ Y.isProjOver
  have hloc : ∀ y : CxPts Y.str σ, ∃ (c : AlgChart Y.str σ Y.dim) (E : ChartMap Y.str σ Y.dim)
      (W : Set (CxPts Y.str σ)) (ε : ℝ), IsOpen W ∧ y ∈ W ∧ W ⊆ c.e.source ∧ 0 < ε ∧ ExphOn.IsExphOn a E W ε :=
    fun y => by
      obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) y
      exact ⟨c, GlobalTheory.ChernReg.ExphLoc.exists_isExphOn F Y.X Y.str σ Y.dim (Y.an σ) a ha c y hc⟩
  choose c E W ε hWo hyW hWc hε hE using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun y _ => mem_iUnion.2 ⟨y, hyW y⟩)
  obtain ⟨v, hv, hvo, hvc⟩ := exists_subset_iUnion_closure_subset (ι := t) isClosed_univ
    (fun i => hWo i) (fun _ _ => Set.toFinite _) (fun y _ => by
      obtain ⟨i, hi, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have key : ∀ s : Finset t, ∃ (E' : ChartMap Y.str σ Y.dim) (W' : Set (CxPts Y.str σ)) (ε' : ℝ),
      IsOpen W' ∧ (⋃ i ∈ s, closure (v i)) ⊆ W' ∧ 0 < ε' ∧ ExphOn.IsExphOn a E' W' ε' := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨_, ∅, 1, isOpen_empty, by simp, one_pos, ExphOn.isExphOn_empty a 1⟩
    | insert i s hi ih =>
      obtain ⟨E₀, W₀, ε₀, hW₀, hK₀, hε₀, hE₀⟩ := ih
      obtain ⟨E₁, W₁, ε₁, hW₁, hK₁, hε₁, hE₁⟩ := GlobalTheory.ChernReg.ExphOn.exists_isExphOn_union F Y.X Y.str σ Y.dim (Y.an σ) a ha (c i) E₀ (E i) W₀
        (W i) (⋃ j ∈ s, closure (v j)) (closure (v i)) ε₀ (ε i) hW₀ (hWo i) (hWc i)
        (s.isCompact_biUnion fun j _ => isClosed_closure.isCompact) isClosed_closure.isCompact hK₀ (hvc i) hε₀
        (hε i) hE₀ (hE i)
      refine ⟨E₁, W₁, ε₁, hW₁, ?_, hε₁, hE₁⟩
      rw [Finset.set_biUnion_insert]
      exact union_comm _ _ ▸ hK₁
  obtain ⟨E', W', ε', -, hK, hε', hE'⟩ := key Finset.univ
  have hU : W' = univ := eq_univ_of_univ_subset fun y _ => hK (by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hv (mem_univ y))
    exact mem_iUnion₂.2 ⟨i, Finset.mem_univ _, subset_closure hi⟩)
  exact GlobalTheory.ChernReg.ExphOn.exists_isExph_of_isExphOn_univ F Y.X Y.str σ Y.dim (Y.an σ) a E' ε' ha hε' (hU ▸ hE')

end GlobalTheory.ChernReg
