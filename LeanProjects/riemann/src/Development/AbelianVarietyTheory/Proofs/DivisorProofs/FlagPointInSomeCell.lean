import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOrbitMapSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermRowsLeadingMinorsNeZeroOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLuDecompositionExistsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

noncomputable def permRowsGL {K : Type} [CommRing K] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) K) :
    GL (Fin N) K :=
  GeneralLinearGroup.mk'' (g.1.submatrix w id) (by
    rw [det_permute]
    exact ((Equiv.Perm.sign w).isUnit.map (Int.castRingHom _)).mul ((isUnit_iff_isUnit_det _).1 g.isUnit))

theorem exists_flagPt_eq_comp_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) {K : Type} [Field K] (g : ι → GL (Fin N) K) :
    ∃ (w : ι → Equiv.Perm (Fin N)) (ψ : CellRing a l →+* K), flagPt a l g = spMap ψ ≫ cell a l w := by
  choose w hw using fun τ => GlobalTheory.GL_exists_perm_rows_leading_minors_ne_zero K N (g τ)
  choose L b hLb hL hb using fun τ => GlobalTheory.T.block_lu_decomposition_exists K N {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}
    (permRowsGL (w τ) (g τ)) fun k hk => (hw τ k hk).isUnit
  have hB (τ : ι) (i j : Fin N) : Below a l τ i j ↔
      ∃ s ∈ {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}, (j : ℕ) < s ∧ s ≤ (i : ℕ) :=
    ⟨fun ⟨k, h₁, h₂⟩ => ⟨_, ⟨k, h₁, rfl⟩, h₂⟩, fun ⟨_, ⟨k, h₁, e⟩, h₂⟩ => ⟨k, h₁, e ▸ h₂⟩⟩
  have e : g = (fun τ => permRowsGL (w τ).symm (L τ)) * b := by
    funext τ
    ext i j
    have := congrArg (fun m : GL (Fin N) K => m.1 ((w τ).symm i) j) (hLb τ)
    simpa [permRowsGL, Matrix.mul_apply] using this
  refine ⟨fun τ => (w τ).symm, _, e.symm ▸ flagPt_eq_comp_cell a l (fun τ => (w τ).symm)
    (fun τ => permRowsGL (w τ).symm (L τ)) b (fun τ i j h => ?_) fun τ i j h => hb τ i j ((hB _ _ _).1 h)⟩
  exact hL τ _ j fun h' => h ((hB _ _ _).2 h')

theorem exists_mem_range_cell (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (x : Part a l) : ∃ w : ι → Equiv.Perm (Fin N), x ∈ Set.range (cell a l w) := by
  obtain ⟨p, rfl⟩ := GlobalTheory.T.flag_orbit_map_surjective ι κ N a l x
  let q : PrimeSpectrum (GLRing ι N) := p
  let ψ : GLRing ι N →+* q.asIdeal.ResidueField := algebraMap _ _
  obtain ⟨w, φ, h⟩ := exists_flagPt_eq_comp_cell a l fun τ => GeneralLinearGroup.map ψ (univGL ι N τ)
  rw [flagPt, evalGL_map_univGL] at h
  let o : Sp q.asIdeal.ResidueField := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have hp : spMap ψ o = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap ψ ⊥ = q.asIdeal
    exact Ideal.ker_algebraMap_residueField _
  refine ⟨w, spMap φ o, ?_⟩
  rw [← hp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]

end GlobalTheory.FlagZ
