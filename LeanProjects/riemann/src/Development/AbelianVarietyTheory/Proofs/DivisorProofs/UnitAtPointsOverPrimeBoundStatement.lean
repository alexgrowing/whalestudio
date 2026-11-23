import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLog
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_at_points_over_prime_bound : GlobalTheory.DetHT.RegLocSt → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (p : ℕ), p.Prime → (p : 𝓞 F) ∈ v.asIdeal → ∀ (h : V.X.functionField) (ρ : ℝ),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → UnitAt (below (z ≫ V.j)) h ∧ Real.log (e.w (TrueGeo.valAt (z ≫ V.j) h)) = ρ) →
    (∀ (x : V.G), ∀ x₀ ∈ U, (V.p x₀).asIdeal = v.asIdeal → V.j x ⤳ x₀ → UnitAt (V.j x) h) ∧
    ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      UnitAt (below (z ≫ V.j)) h ∧ Real.log (e.w (TrueGeo.valAt (z ≫ V.j) h)) = ρ := by
  first | exact @GlobalTheory.NormExt.main | exact GlobalTheory.NormExt.main | (intros; apply GlobalTheory.NormExt.main <;> assumption)
