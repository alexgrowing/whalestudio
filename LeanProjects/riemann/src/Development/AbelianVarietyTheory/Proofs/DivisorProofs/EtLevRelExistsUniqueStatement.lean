import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (exact GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (intros; apply GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique  <;> assumption)
