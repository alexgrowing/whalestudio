import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DiscreteTopologySpanOfLinearIndependent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isLatBasis_of_isLatFam : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  intro n g B K b₀ hK hb₀
  obtain ⟨H, hH⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH]; exact H.zero_mem
  obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hcont : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hev : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ K b₀ → w = 0 := by
    filter_upwards [hcont.eventually hζ] with w hw hwK
    rw [← hζ0]; exact hw.1 hwK
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule H
  have hL : ∀ w, w ∈ L ↔ w ∈ K b₀ := fun w => by
    rw [← hH]; rfl
  haveI : DiscreteTopology L := by
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.1 hev
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have : ({0} : Set L) = Subtype.val ⁻¹' U := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact h0U
      · intro hx; exact Subtype.ext (hU hx ((hL x).1 x.2))
    rw [this]; exact hUo.preimage continuous_subtype_val
  let bs := Module.finBasis ℤ L
  refine ⟨Module.finrank ℤ L, fun i => (bs i : Fin g → ℂ), GlobalTheory.linearIndependent_real_coe_basis bs, fun w => ?_⟩
  have hsp := GlobalTheory.span_range_coe_basis bs
  have hw : w ∈ L ↔ w ∈ Submodule.span ℤ (Set.range fun i => (bs i : Fin g → ℂ)) := by rw [hsp]
  rw [← hL, hw, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩

end GlobalTheory.ShFam.Hor.LogCh
