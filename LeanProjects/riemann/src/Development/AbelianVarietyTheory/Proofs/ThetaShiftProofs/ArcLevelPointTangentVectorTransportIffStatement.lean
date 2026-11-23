import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (y' : Sp ℂ⸨X⸩ ⟶ S') (y : Sp ℂ⸨X⸩ ⟶ S) (Φ' : GenPts A t' y') (Φ : GenPts A t y), w.IsGen → GenPts.Rel m w Φ' Φ → (∀ (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G) (p : Over.mk y ⟶ t.G) la, p'.left ≫ m.φ = p.left → (Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la)) ∧ ∀ z₀ (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y), ν' ≫ pullback.fst _ _ ≫ m.φ = ν ≫ pullback.fst _ _ → ν' ≫ pullback.snd _ _ = ν ≫ pullback.snd _ _ → (Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ ν) := by
  first | exact @GlobalTheory.LevelTransport.levelPt_isTan_iff | exact GlobalTheory.LevelTransport.levelPt_isTan_iff | (intros; apply GlobalTheory.LevelTransport.levelPt_isTan_iff <;> assumption)
