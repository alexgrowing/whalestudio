import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeTwoDifferCoboundary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCocycles_degreeTwo_differ_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  first | exact @GlobalTheory.PDForm.ClsTwo.cob_of_class_eq | exact GlobalTheory.PDForm.ClsTwo.cob_of_class_eq | (intros; apply GlobalTheory.PDForm.ClsTwo.cob_of_class_eq <;> assumption)
