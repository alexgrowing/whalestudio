import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIso
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationValues_transport_fieldIso : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N), ∃ (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ ∧ (∀ x, I.h x = 1) ∧ I.lam = 1 ∧ (∀ χ, ν'.eX (I.e χ) = ν.eX χ) ∧ ν'.th = ν.th ∧ ν'.rg = e ν.rg ∧ (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) ∧ ∀ (k : ℕ) (s : Fam D F k), ∃ s' : Fam D F' k, (∀ f, ν.FamV s f → ∃ f', ν'.FamV s' f' ∧ ∀ α x, f' (I.e α) (I.φ x) = e (f α x)) ∧ ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ α, jc ν' s' gm' (I.e α) = dualMap (e : F →+* F') (jc ν s gm α) := by
  first | exact @GlobalTheory.MBLow.FieldIso.transport_iso | exact GlobalTheory.MBLow.FieldIso.transport_iso | (intros; apply GlobalTheory.MBLow.FieldIso.transport_iso <;> assumption)
