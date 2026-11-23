import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPushStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff

noncomputable section

namespace SquareStatements.Sing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt IsValueAt)

theorem isValueAt_valAt_of_regAt {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    {x : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal w) s) : IsValueAt x s w (valAt x s w) := by
  obtain ⟨d, g, h, hg, hh, hQ, hgh⟩ := hs
  have hwh : (MvPolynomial.eval w) ((MvPolynomial.map (Int.castRingHom ℂ)) h) ≠ 0 := by
    intro h0
    apply hQ
    apply GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero w hh
    rw [MvPolynomial.eval_map] at h0
    simpa [MvPolynomial.aeval_def] using h0
  have hxh : (MvPolynomial.aeval x) h ≠ 0 := by
    intro h0
    exact hwh (hw.2 h (GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have hex : ∃ v, IsValueAt x s w v := ⟨_, d, g, h, hg, hh, hxh, hgh, hwh, rfl⟩
  unfold GroundTheory.Heights₂.Heights.LowerBoundFree.valAt
  rw [dif_pos hex]
  exact hex.choose_spec

theorem c0 : C0 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 𝔐' pr j z w hO hw
  obtain ⟨hd, hf, -, -, -⟩ := hO
  obtain ⟨-, -, hval⟩ := GlobalTheory.T.dominating_regular_push 𝔐'.X 𝔐.X Φ M.Ω 𝔐'.ξ 𝔐.ξ pr (algebraMap M.Ω Φ) hd 𝔐'.tie.gen
  have hval' : ∀ (a : M.Ω) (r : ℂ), ValAt 𝔐.ξ (z ≫ pr) a r → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ a) r :=
    fun a r => hval z a r (𝔐'.all _)
  have hco : CoordsAt 𝔐.ξ M.x (z ≫ pr) (basePart M.blk w) :=
    GlobalTheory.T.dominating_coords_reindexed 𝔐'.X 𝔐.X Φ M.Ω 𝔐'.ξ 𝔐.ξ pr (algebraMap M.Ω Φ) (NonPluckerBlocks M.blk) K (baseIdx ι M.blk) ι M.x y
      Subtype.val (fun _ => Equiv.refl _) hd 𝔐.tie 𝔐'.all (fun k a => M.y_base ⟨k, a⟩)
      (fun z' a r h' => hval z' a r (𝔐'.all _) h') z w hw
  refine ⟨hco, GlobalTheory.CompanionTheory.Ar.Chg.mem_abLocus_iff 𝔐 𝔐' pr hf (centre z), hval', fun s hs => hval' _ _ ?_⟩
  have hm : basePart M.blk w ∈ mcPts (mCoordIdeal M.x) :=
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).2 ⟨z ≫ pr, 𝔐.all _, hco⟩
  exact (GlobalTheory.T.valAt_iff_value_at 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie (z ≫ pr) _ (𝔐.all _) hco s _).2
    (isValueAt_valAt_of_regAt hm hs)

end SquareStatements.Sing
