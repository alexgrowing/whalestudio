import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem isLattice_of_eq_span_frac_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) (M N : Submodule (𝓞 K) V)
    (h : M = Submodule.span (𝓞 K) {x | ∃ a ∈ I, ∃ y ∈ N, x = (a : K) • y})
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K N := by
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ (0 : K) := by
    by_contra hc
    push_neg at hc
    exact hI (FractionalIdeal.eq_zero_iff.2 hc)
  refine ⟨?_, ?_⟩
  · let f : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V a).restrictScalars (𝓞 K)
    have hf : Function.Injective f := fun x y hxy => smul_right_injective V ha0 hxy
    have hle : N.map f ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      rw [h]
      exact Submodule.subset_span ⟨a, haI, y, hy, rfl⟩
    have hfg : (N.map f).FG := Submodule.FG.of_le hM.fg hle
    exact Submodule.fg_of_fg_map_injective f hf hfg
  · rw [eq_top_iff, ← hM.span_eq_top, Submodule.span_le, h]
    intro x hx
    have : Submodule.span (𝓞 K) {x | ∃ a ∈ I, ∃ y ∈ N, x = (a : K) • y} ≤
        (Submodule.span K (N : Set V)).restrictScalars (𝓞 K) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, _, y, hy, rfl⟩
      exact Submodule.smul_mem (Submodule.span K (N : Set V)) b (Submodule.subset_span hy)
    exact this hx

theorem isLattice_comap_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W]
    [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (e : W ≃ₗ[K] V) (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.comap ((e : W →ₗ[K] V).restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective ((e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.injective ?_
    rw [Submodule.map_comap_eq_of_surjective
      (f := (e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.surjective]
    exact hN.fg
  · apply Submodule.map_injective_of_injective (f := (e : W →ₗ[K] V)) e.injective
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← hN.span_eq_top]
    congr 1
    exact Set.image_preimage_eq _ e.surjective

theorem nuLat_comap_isLattice : ∀ (D : D7) (L : SizeData₂ D), Formalism.BasicNotions.DV.NprimeDef D L → ∀ u, Submodule.IsLattice D.what₂.LL (D.div.Nu u).L → ∀ (d : ℕ) (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Submodule.IsLattice D.what₂.LL ((L.NuLat u).comap ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))) := by
  intro D L hdef u hL d e
  have hI : Formalism.BasicNotions.DV.Iu D L u ≠ 0 := by
    unfold Formalism.BasicNotions.DV.Iu
    rw [Finset.prod_ne_zero_iff]
    intro w _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq w).ne_bot)
  exact isLattice_comap_equiv e _
    (isLattice_of_eq_span_frac_smul (Formalism.BasicNotions.DV.Iu D L u) hI _ _ (hdef u) hL)

end GlobalTheory.ColRows
