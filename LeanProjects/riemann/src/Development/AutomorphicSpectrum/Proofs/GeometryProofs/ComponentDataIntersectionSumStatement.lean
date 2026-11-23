import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_data_intersection_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (S₀ : Finset ℕ) (𝔐 : HodgeCpt Y S₀ Dc.y) (bg sm : CMType H → CMType H ⊕ CMType H) (i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li) (s : CMType H → Fin (Dc.N - Dc.j) → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), (∀ τ, Function.Injective (i τ)) → (∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)) → (∀ τ, bg τ ≠ sm τ) → (∀ τ, labelRk D (bg τ) = Dc.j) → (∀ τ, labelRk D (sm τ) = Dc.N - Dc.j) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsVB Dc.N ⊤) → (∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat) → (∀ τ, LinearIndependent Ω (s τ)) → (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y aMu e₀ → ∃ Hd : HodgeData Dc, ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BigBlock.main | exact GlobalTheory.CompanionTheory.Ar.BigBlock.main | (intros; apply GlobalTheory.CompanionTheory.Ar.BigBlock.main <;> assumption)
