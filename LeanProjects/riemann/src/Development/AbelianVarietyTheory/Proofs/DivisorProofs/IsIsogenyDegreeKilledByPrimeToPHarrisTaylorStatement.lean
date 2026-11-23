import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyDegreeKilledByPrimeToPHarrisTaylor
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), (∀ c : 𝓞 D.F, c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n))) → ∀ (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (K : Over S) (i : K ⟶ o.A), Mono i → (∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
  first | (exact @GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy) | (exact GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy) | (intros; apply GlobalTheory.IwLevel.PrimeToP.isIsogDeg_killedBy <;> assumption)
