import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationRayEventually
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_ray_eventually : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (ψ φ : InvFun (𝓞 E)) (k : ℕ), (∀ i, PolRay ψ φ k (C i)) → ∃ bb N T₀ : ℕ, 0 < bb ∧ 0 < N ∧ ∀ T, T₀ ≤ T → ∀ i, ∃ BD : EffCartierData (C i).X, IsPol (comb (N * T) ψ bb φ) (N * T * k) (C i) BD := by
  first | exact @GlobalTheory.TorRef.exists_common_polRay | exact GlobalTheory.TorRef.exists_common_polRay | (intros; apply GlobalTheory.TorRef.exists_common_polRay <;> assumption)
