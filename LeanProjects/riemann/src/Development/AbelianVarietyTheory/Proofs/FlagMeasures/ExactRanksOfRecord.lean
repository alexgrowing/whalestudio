import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExactStatement

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem exact_ranks_of_record : ∀ D : D7, (∀ i, StandardLattice.SplitsF D (D.host.g i)) → StandardLattice.volY0 D = StandardLattice.massI D D.R.r → StandardLattice.FactDstar D → (∀ u, (D.duS u : ℝ) = StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → letI := D.host.cmStar; ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V), h.IsSymm → (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word, (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)) * (∏ τ, Formalism.MainNotions.S.vand (fun i : Fin D.R.k => (((D.hcW u τ).u i : ℚ) : ℝ)) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) ∧ (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r → D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, (∏ i ∈ Finset.range D.R.r, ((Ideal.absNorm p.asIdeal : ℝ) ^ D.R.r - (Ideal.absNorm p.asIdeal : ℝ) ^ i)) / ((Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))) * ∏ τ, D.dsig τ) := by
  intro D hsp hvol hD hdu V _ _ _ _ h L hs
  letI := D.host.cmStar
  have hmass : ∀ n, Formalism.HermitianLatticesTheory.IsOrthoLattice h L n → Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D n :=
    fun n ho => StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram n V h L ho
  have hcol := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1)) hsp
  have hrow := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => (∏ i ∈ Finset.range D.R.r, (x ^ D.R.r - x ^ i)) /
    (x ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * x ^ (D.R.k * (D.R.k - 1) / 2))) hsp
  beta_reduce at hcol hrow
  obtain ⟨hc0, hr0⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 0
  obtain ⟨hc1, hr1⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 1
  refine ⟨fun ho u => ?_, fun ho => ?_⟩
  · rw [hdu u, hmass _ ho, hcol]
    unfold StandardLattice.duStarU StandardLattice.duStarP StandardLattice.idxPi
    rw [hc0, hc1]
    rfl
  · rw [show D.what₂.Dstar = StandardLattice.DstarD D from hD, hmass _ ho, hrow]
    unfold StandardLattice.DstarD StandardLattice.DstarP StandardLattice.idxSig
    rw [hvol, hr0, hr1]

end GlobalTheory
