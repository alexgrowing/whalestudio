import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEquationsHeightSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_equations_height_sum : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (D : CartierDiv Z) (e : ∀ v : HeightOneSpectrum (𝓞 F), Ext v) (l : HeightOneSpectrum (𝓞 F) → {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} → ℝ), (∀ v y (yt : Sp (e v).O ⟶ Z), spMap (e v).O.subtype ≫ yt = y.1 → ∃ g : Z.functionFieldˣ, D.IsEqn (yt (IsLocalRing.closedPoint (e v).O)) g ∧ l v y = Real.log ((e v).w (valAt y.1 (g : Z.functionField)))) → ∑ᶠ z : Z, (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ v, ∑ᶠ y, l v y := by
  first | exact @GlobalTheory.TrueGeo.FinSum.main | exact GlobalTheory.TrueGeo.FinSum.main | (intros; apply GlobalTheory.TrueGeo.FinSum.main <;> assumption)
