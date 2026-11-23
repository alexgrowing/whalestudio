import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSchemeRepresentingEtaleLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevScheme) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevScheme <;> assumption)
