import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_val_at_vert_factor_eq_norm_mul_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value <;> assumption)
