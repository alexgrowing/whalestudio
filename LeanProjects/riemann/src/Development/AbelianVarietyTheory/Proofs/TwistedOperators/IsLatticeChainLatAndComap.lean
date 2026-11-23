import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Imports
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsAlt

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff]
    intro v _
    have hv : v = inX k n c (fun r => v (Sum.inl r)) +
        ∑ i : Fin c, (v (Sum.inr i) / (ϖ : k) ^ ((i : ℕ) + 1)) •
          ((ϖ : k) ^ ((i : ℕ) + 1) • aux k n i) := by
      have h : ∀ i : Fin c, (v (Sum.inr i) / (ϖ : k) ^ ((i : ℕ) + 1)) •
          ((ϖ : k) ^ ((i : ℕ) + 1) • aux k n i) = v (Sum.inr i) • aux k n i := by
        intro i
        rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hϖ)]
      simp only [h]
      funext j
      rcases j with r | j
      · simp [inX_apply, aux, Finset.sum_apply]
      · simp [inX_apply, aux, Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (scaled_basis_mem_chainLattice ϖ L i)))
    obtain ⟨a, ha, hav⟩ := exists_smul_mem (K := k) L (v := fun r => v (Sum.inl r))
      (by rw [hL.span_eq_top]; trivial)
    have h1 : algebraMap 𝒪[k] k a ≠ 0 := by simpa using ha
    have : inX k n c (fun r => v (Sum.inl r)) =
        (algebraMap 𝒪[k] k a)⁻¹ • inX k n c (a • fun r => v (Sum.inl r)) := by
      rw [map_smul, ← algebraMap_smul k a, smul_smul, inv_mul_cancel₀ h1, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (inX_mem_chainLat.2 hav))
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · refine span_eq_top_of_smul_mem _ fun v => ?_
    obtain ⟨a, ha, hav⟩ := exists_smul_mem (K := k) Λ (v := inX k n c v)
      (by rw [hΛ.span_eq_top]; trivial)
    exact ⟨a, ha, by rw [Submodule.mem_comap, map_smul]; exact hav⟩

end GlobalTheory.RootEx.ChainLattice
