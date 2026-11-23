import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LebesgueSelfdualForDotCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_level_group_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S) (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct <;> assumption)
