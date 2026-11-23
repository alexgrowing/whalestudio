import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitelyGeneratedLatticeFullEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeIsometricEmbeddingEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsometricEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeLeUnderEmbeddingStatement
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory

theorem siegel_sublattice_line : GlobalTheory.Published.AbsoluteSiegel → ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (h : HermFam K (Fin m → K)) (L W : Submodule (𝓞 K) (Fin m → K)), Full L → GlobalTheory.Published.ConjInv h → W ≤ L → 1 ≤ latRank K W → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin m → K')) (x : Fin m → K'), IsBC h h' ∧ x ≠ 0 ∧ deg h W / latRank K W - Real.log (latRank K W) / 2 - 1 ≤ deg h' (lineLat (latBC K' L) x) := by
  intro HS K _ _ m h L W hL hc hWL hr
  have hWfg : W.FG := Submodule.FG.of_le hL.1 hWL
  obtain ⟨α, hαi, hfull, hmap⟩ := GlobalTheory.T.finitely_generated_lattice_full_embedding K m W hWfg
  let hW : HermFam K (Fin (latRank K W) → K) :=
    { form := fun σ y z => h.form σ (α y) (α z)
      add_right := fun σ x y z => by simp only [map_add]; exact h.add_right σ _ _ _
      smul_right := fun σ a x y => by simp only [map_smul]; exact h.smul_right σ a _ _
      conj_symm := fun σ x y => h.conj_symm σ _ _
      posDef := fun σ k v hv => h.posDef σ k (fun i => α (v i)) (hv.map' α (LinearMap.ker_eq_bot.mpr hαi)) }
  have hWc : GlobalTheory.Published.ConjInv hW := fun σ y z => hc σ (α y) (α z)
  have hdeg : deg hW (W.comap (α.restrictScalars (𝓞 K))) = deg h W := by
    have := GlobalTheory.T.degree_isometric_embedding_eq K _ m hW h α hαi (fun _ _ _ => rfl) _ hfull.1
    rwa [hmap] at this
  obtain ⟨K', i1, i2, i3, hW', x', hBC', hx', hineq⟩ := HS K (latRank K W) hW (W.comap (α.restrictScalars (𝓞 K))) hr hWc hfull 1 one_pos
  obtain ⟨⟨h', hBC⟩, hLf, -⟩ := GlobalTheory.T.hermitian_lattice_base_change K K' m h L hL.1
  obtain ⟨β, hβi, hβf, hβα⟩ := GlobalTheory.T.base_change_isometric_embedding K K' _ m α h hW h' hW' (fun _ _ _ => rfl) hBC hBC'
  have hM' : Full (latBC K' (W.comap (α.restrictScalars (𝓞 K)))) :=
    (GlobalTheory.T.hermitian_lattice_base_change K K' _ hW _ hfull.1).2.1 hfull
  have hmaps : ∀ y ∈ latBC K' (W.comap (α.restrictScalars (𝓞 K))), β y ∈ latBC K' L := by
    intro y hy
    have hle : latBC K' (W.comap (α.restrictScalars (𝓞 K))) ≤ (latBC K' L).comap (β.restrictScalars (𝓞 K')) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, hz, rfl⟩
      show β _ ∈ latBC K' L
      rw [hβα z]
      exact Submodule.subset_span ⟨α z, hWL hz, rfl⟩
    exact hle hy
  have hD := GlobalTheory.T.line_degree_le_under_embedding K' _ m hW' h' β _ (latBC K' L) x' hβi hβf hM' (hLf hL) hmaps hx'
  refine ⟨K', i1, i2, i3, h', β x', hBC, fun e => hx' (hβi (by rw [e, map_zero])), ?_⟩
  rw [← hdeg]; linarith

end GlobalTheory
