import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTwistedCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_twisted_cover : PolMapSt → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F} (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X) (φ : InvFun (𝓞 E)) (m : ℕ) (BD : ∀ i, EffCartierData (C i).X), IsTwInv H φ → IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → (∀ i, IsChartOf Z (C i) (a i) (b i) (u i)) → (∀ i, IsPol φ m (C i) (BD i)) → ∀ i j, (BD i).idealSheaf.comap (pullback.fst (u i) (u j)) = (BD j).idealSheaf.comap (pullback.snd (u i) (u j)) := by
  first | exact @GlobalTheory.TorRef.charts_divisor_compat | exact GlobalTheory.TorRef.charts_divisor_compat | (intros; apply GlobalTheory.TorRef.charts_divisor_compat <;> assumption)
