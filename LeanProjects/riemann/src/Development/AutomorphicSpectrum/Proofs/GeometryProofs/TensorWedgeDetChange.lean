import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.TopWedge

theorem exists_form_tprod_wedge (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type)
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e : ∀ τ, Fin n → V τ)
    (hli : ∀ τ, LinearIndependent Ω (e τ)) (hspan : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) :
    ∃ Φ : (PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) →ₗ[Ω] Ω,
      Φ (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ)) = 1 := by
  classical
  let b : ∀ τ, Module.Basis (Fin n) Ω (V τ) := fun τ => Module.Basis.mk (hli τ) (hspan τ).ge
  let φ : ∀ τ, ⋀[Ω]^n (V τ) →ₗ[Ω] Ω := fun τ => exteriorPower.alternatingMapLinearEquiv (b τ).det
  have hφ : ∀ τ, φ τ (exteriorPower.ιMulti Ω n (e τ)) = 1 := fun τ => by
    have hb : (⇑(b τ) : Fin n → V τ) = e τ := Module.Basis.coe_mk _ _
    simp only [φ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [← hb]
    exact (b τ).det_self
  refine ⟨PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra Ω Ψ Ω).compLinearMap φ), ?_⟩
  rw [PiTensorProduct.lift.tprod]
  simp [hφ]

theorem eq_mul_prod_det : ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e e' : ∀ τ, Fin n → V τ) (T : ∀ τ, Matrix (Fin n) (Fin n) Ω) (a a' : Ω), (∀ τ, LinearIndependent Ω (e τ)) → (∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) → (∀ τ q, e' τ q = ∑ p, T τ p q • e τ p) → a • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) = a' • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) → a = a' * ∏ τ, (T τ).det := by
  intro Ψ _ Ω _ V _ _ n e e' T a a' hli hspan hT h
  classical
  obtain ⟨Φ, hΦ⟩ := exists_form_tprod_wedge Ψ Ω V n e hli hspan
  have hq : ∀ τ, exteriorPower.ιMulti Ω n (e' τ) = (T τ).det • exteriorPower.ιMulti Ω n (e τ) := fun τ => by
    rw [← GlobalTheory.CompanionTheory.Ar.BigBlock.iotaMulti_comb]
    congr 1
    funext q
    exact hT τ q
  have htp : (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ)) =
      (∏ τ, (T τ).det) • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ)) := by
    simp_rw [hq]
    exact MultilinearMap.map_smul_univ _ _ _
  have h2 := congrArg Φ h
  rw [htp, map_smul, map_smul, map_smul, hΦ] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.TopWedge
