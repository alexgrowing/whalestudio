import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

theorem Proportional.basicOpen_le_chart {R : Type} [CommRing R] {X W : Scheme.{0}} {L : LB X} {m : ℕ}
    {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) :
    W.basicOpen ((g.appLE (L.U k) A hk).hom ((σ i).f k)) ≤ ψ ⁻¹ᵁ chart R m i := by
  intro z hz
  obtain ⟨i', hi'⟩ := (isCoordFamily_pullRatio ψ).exists_mem z
  have hA : z ∈ A := W.basicOpen_le _ hz
  have e := h (A ⊓ ψ ⁻¹ᵁ chart R m i') k (inf_le_left.trans hk) i' inf_le_right i
  have e' := congrArg W.basicOpen e
  rw [Scheme.basicOpen_mul, basicOpen_pullRatio, Scheme.basicOpen_appLE] at e'
  rw [Scheme.basicOpen_appLE] at hz
  have hz' : z ∈ (A ⊓ ψ ⁻¹ᵁ chart R m i') ⊓ g ⁻¹ᵁ X.basicOpen ((σ i).f k) := ⟨⟨hA, hi'⟩, hz.2⟩
  exact (e'.le hz').1.2

theorem eq_of_proportional :
    ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  intro R _ X W L m σ g ψ ψ' hG hs h h'
  refine hom_ext hs fun y => ?_
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hG.1.ge (Set.mem_univ y))
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAk⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hk (g ⁻¹ᵁ L.U k).isOpen
  have hAk' : A ≤ g ⁻¹ᵁ L.U k := hAk
  have hsp := hG.2 k ⟨A, hA⟩ hAk'
  have hsp' : Ideal.span (Set.range fun j => (g.appLE (L.U k) A hAk').hom ((σ j).f k)) = ⊤ := hsp.symm
  have hcov := (IsAffineOpen.self_le_iSup_basicOpen_iff hA).2 hsp'
  obtain ⟨⟨_, i, rfl⟩, hi⟩ := Opens.mem_iSup.1 (hcov hyA)
  have hB := W.basicOpen_le ((g.appLE (L.U k) A hAk').hom ((σ i).f k))
  refine ⟨_, hi, i, h.basicOpen_le_chart A k hAk' i, h'.basicOpen_le_chart A k hAk' i, fun j => ?_⟩
  have hu : IsUnit ((g.appLE (L.U k) _ (hB.trans hAk')).hom ((σ i).f k)) := by
    rw [← resG_appLE g hAk' hB]
    exact RingedSpace.isUnit_res_basicOpen _ _
  exact hu.mul_right_cancel ((h _ k _ i _ j).symm.trans (h' _ k _ i _ j))

end GlobalTheory.ProjBlowup
