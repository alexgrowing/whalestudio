import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

namespace GlobalTheory

theorem pullback_fromSpec_compact_affineCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → CompactSpace ↑(pullback t.G.hom U.2.fromSpec : Scheme.{0}) ∧ (∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i)) ∧ ⨆ i, pullback.fst t.G.hom U.2.fromSpec ⁻¹ᵁ W i = ⊤ := by
  intro E _ _ _ H X t hP U J W hW hcov
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hU : IsAffineOpen U.1 := U.2
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have : IsOpenImmersion (pullback.fst t.G.hom hU.fromSpec) := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd t.G.hom hU.fromSpec)
  · intro I hI
    have := GlobalTheory.isAffineHom_diagonal_of_isSeparated (pullback.snd t.G.hom hU.fromSpec)
    refine GlobalTheory.isAffineOpen_finset_biInf (fun i => ?_) I hI
    have hle : W i ≤ (pullback.fst t.G.hom hU.fromSpec).opensRange := by
      intro x hx
      have hx' : x ∈ t.G.hom ⁻¹ᵁ U.1 := hcov ▸ (le_iSup W i) hx
      have hy : t.G.hom x ∈ Set.range hU.fromSpec := by
        rw [hU.range_fromSpec]; exact hx'
      obtain ⟨y, hy⟩ := hy
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨z, hz⟩
    rw [← (pullback.fst t.G.hom hU.fromSpec).isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hle]
    exact hW i
  · rw [← Scheme.Hom.preimage_iSup, hcov, ← Scheme.Hom.comp_preimage, pullback.condition,
      Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

end GlobalTheory
