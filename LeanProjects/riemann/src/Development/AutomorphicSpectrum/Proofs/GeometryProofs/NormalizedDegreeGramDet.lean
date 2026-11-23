import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree

open scoped ComplexOrder in

theorem gramDet_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ)
    {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem normDegree_top_eq_mean_gramDet : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (n : ℕ) (e : Fin n → B.carrier), LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → B.normDegree ⊤ = -(1 / 2) * mean L (fun σ => Real.log ‖B.gramDet σ e‖) := by
  intro L _ _ B n e hli hspan
  let s : Fin n → (⊤ : Submodule (𝓞 L) B.carrier) := fun i => ⟨e i, Submodule.mem_top⟩
  have hs : LinearIndependent (𝓞 L) s :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 L) B.carrier).subtype hli
  have hcard : Fintype.card (Fin n) = B.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top,
      Module.finrank_eq_card_basis (Module.Basis.mk hli hspan.ge), Fintype.card_fin]
  have hsp : Submodule.span (𝓞 L) (Set.range s) = ⊤ := by
    have hmap : (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := hx'
    exact hy
  have hone : Nat.card ((⊤ : Submodule (𝓞 L) B.carrier) ⧸ Submodule.span (𝓞 L) (Set.range s)) = 1 := by
    rw [hsp]
    exact Nat.card_unique
  have hg : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun i => ((s i : (⊤ : Submodule (𝓞 L) B.carrier)) : B.carrier)) = ‖B.gramDet σ e‖ :=
    fun σ => gramDet_eq_norm B σ hli
  rw [HermitianBundle.normDegree, B.degree_eq_of_linearIndependent ⊤ hs hcard,
    hone, Nat.cast_one, Real.log_one, zero_sub, mean]
  simp only [hg]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree
