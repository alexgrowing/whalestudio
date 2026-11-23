import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem fibreLat_of_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ), IsOver 𝔐 z κ p → FibreLat Xo.univ.t p R → FibreLat 𝔐.t z R := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z κ p g Λ _ _ R hov hF
  obtain ⟨x, hxj, hxp, -⟩ := hov
  have hA := (GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Xo.univ.t Y.oF.t _ g Λ R R x).1 ⟨Y.m0.toSABMap⟩
  have hB := (GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t Y.oF.t _ g Λ R R x).1 ⟨Y.m⟩
  have hC := (GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t 𝔐.t _ g Λ R R z).1 ⟨𝔐.m⟩
  rw [← hxp] at hF
  have h2 := hB.1 (hA.2 hF)
  apply hC.2
  have hj : x ≫ Y.j = z ≫ 𝔐.f := hxj
  rw [← hj]
  exact h2

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
