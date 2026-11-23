import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisLevelZeroSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_level_zero_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (_ : PELUnif (maximalIdeal R) t) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), N = 0 →
    BasisAlong t.G t.PP.L N (toBase (algebraMap R (FractionRing R))) b →
    ∀ (F : Type) [Field F] (ψ : R →+* F), Function.Injective ψ →
    ∀ s : LB.Sec (LPow t.G t.PP.L (N : ℤ) (Over.mk (spMap ψ))), ∃ c, Lin t.G t.PP.L N (toBase ψ) b c s := by
  first | exact @GlobalTheory.TorRef.ZeroPow.span_of_basisAlong_zero | exact GlobalTheory.TorRef.ZeroPow.span_of_basisAlong_zero | (intros; apply GlobalTheory.TorRef.ZeroPow.span_of_basisAlong_zero <;> assumption)
