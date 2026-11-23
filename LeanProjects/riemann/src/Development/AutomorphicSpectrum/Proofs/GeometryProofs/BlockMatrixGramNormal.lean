import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem quotNormSq_eq_of_blockFrame : ∀ (N j : ℕ) (hj : j ≤ N) (G G' T : Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ), G.PosDef → G' = Tᴴ * G * T → (∀ a a', T (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0) → (∀ k a, T (tailIdx hj k) (headIdx hj a) = 0) → (∀ k k', T (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0) → (∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0) → (∀ k k', G' (tailIdx hj k) (tailIdx hj k') = Γ k k') → quotNormSq hj G = Γ.det.re := by
  intro N j hj G G' T Γ hG hG' hT1 hT2 hT3 hG'1 hG'2
  obtain ⟨e, hel, her⟩ : ∃ e : Fin j ⊕ Fin (N - j) ≃ Fin N,
      (∀ a, e (Sum.inl a) = headIdx hj a) ∧ ∀ k, e (Sum.inr k) = tailIdx hj k :=
    ⟨finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hj)),
      fun a => by ext; simp [headIdx],
      fun k => by ext; simp [tailIdx]⟩
  have hhinj : Function.Injective (headIdx hj) := by
    intro a a' h
    rw [← hel, ← hel] at h
    exact Sum.inl_injective (e.injective h)
  have hht : ∀ a k, headIdx hj a ≠ tailIdx hj k := by
    intro a k h
    rw [← hel, ← her] at h
    exact Sum.inl_ne_inr (e.injective h)
  have hblocks : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.submatrix e e =
      Matrix.fromBlocks (M.submatrix (headIdx hj) (headIdx hj))
        (M.submatrix (headIdx hj) (tailIdx hj))
        (M.submatrix (tailIdx hj) (headIdx hj)) (M.submatrix (tailIdx hj) (tailIdx hj)) := by
    intro M
    ext (a | k) (a' | k') <;> simp [hel, her]
  have hdet : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.det = (M.submatrix e e).det := fun M =>
    (Matrix.det_submatrix_equiv_self e M).symm
  have hTdet : T.det = 1 := by
    have h1 : T.submatrix (headIdx hj) (headIdx hj) = 1 := by
      ext a a'; simp [hT1, Matrix.one_apply]
    have h0 : T.submatrix (tailIdx hj) (headIdx hj) = 0 := by
      ext k a; simp [hT2]
    have h2 : T.submatrix (tailIdx hj) (tailIdx hj) = 1 := by
      ext k k'; simp [hT3, Matrix.one_apply]
    rw [hdet T, hblocks T, h1, h0, h2, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hdetG : G'.det = G.det := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hTdet]
    simp
  have hcol : T.submatrix id (headIdx hj) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix id (headIdx hj) := by
    ext y a'
    obtain ⟨z, rfl⟩ := e.surjective y
    rcases z with a | k
    · simp [hel, hT1, Matrix.one_apply, hhinj.eq_iff]
    · simp [her, hT2, Matrix.one_apply, (hht a' k).symm]
  have key : ∀ M : Matrix (Fin N) (Fin N) ℂ,
      (Mᴴ * G * M).submatrix (headIdx hj) (headIdx hj) =
        (M.submatrix id (headIdx hj))ᴴ * G * M.submatrix id (headIdx hj) := by
    intro M
    first
      | rfl
      | (ext a a'; simp [Matrix.mul_apply, Matrix.conjTranspose_apply])
  have hhh : G'.submatrix (headIdx hj) (headIdx hj) = G.submatrix (headIdx hj) (headIdx hj) := by
    rw [hG', key T, hcol, ← key 1]
    simp
  have hht' : G'.submatrix (headIdx hj) (tailIdx hj) = 0 := by
    ext a k; simp [hG'1]
  have htt : G'.submatrix (tailIdx hj) (tailIdx hj) = Γ := by
    ext k k'; simp [hG'2]
  have hdetblock : G.det = (G.submatrix (headIdx hj) (headIdx hj)).det * Γ.det := by
    rw [← hdetG, hdet G', hblocks G', hht', htt, Matrix.det_fromBlocks_zero₁₂, hhh]
  have hpos : 0 < (G.submatrix (headIdx hj) (headIdx hj)).det :=
    (hG.submatrix hhinj).det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  unfold quotNormSq
  rw [hdetblock, Complex.mul_re, ← him, zero_mul, sub_zero]
  exact mul_div_cancel_left₀ _ hre.ne'

end GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame
