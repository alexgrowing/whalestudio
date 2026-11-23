import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
open GlobalTheory.ShFam.Hor.LogCh

set_option autoImplicit false

open Topology

namespace GlobalTheory.LatReal

theorem isRealBasis_of_isLatFam : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) →
    LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  intro n g r B K b₀ lam hF hb hspan hli hK
  have hmemL : ∀ w, w ∈ Submodule.span ℤ (Set.range lam) ↔ w ∈ K b₀ := by
    intro w
    rw [Submodule.mem_span_range_iff_exists_fun, hK]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.symm⟩
  have hsub : K b₀ ⊆ Submodule.span ℝ (Set.range lam) := by
    intro w hw
    obtain ⟨k, rfl⟩ := (hK w).1 hw
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have htop : Submodule.span ℝ (Set.range lam) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 hsub
  refine ⟨?_, htop⟩
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := (hK 0).2 ⟨0, by simp⟩
  obtain ⟨ζ, hζ0, -, hev⟩ := hF.2.2.2 b₀ hb 0 h0
  have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' 0 (b₀, 0) rfl
  have hev' : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (w ∈ K b₀ ↔ w = 0) := by
    filter_upwards [ht.eventually hev] with w hw
    simpa [hζ0] using hw
  obtain ⟨U, hU, hUo, hU0⟩ := mem_nhds_iff.1 hev'
  set L := Submodule.span ℤ (Set.range lam) with hLdef
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [isOpen_induced_iff]
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext ((hU hx).1 ((hmemL x).1 x.2))
    · rintro rfl
      exact hU0
  have hLset : (L : Set (Fin g → ℂ)) = K b₀ := by
    ext w
    exact hmemL w
  haveI : IsZLattice ℝ L := ⟨by rw [hLset, hspan]⟩
  have hrank := ZLattice.rank ℝ L
  have hcard : Module.finrank ℤ L = r := by
    rw [Module.finrank_eq_card_basis (Module.Basis.span hli)]
    simp
  apply linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge
  rw [Fintype.card_fin]
  omega

end GlobalTheory.LatReal
