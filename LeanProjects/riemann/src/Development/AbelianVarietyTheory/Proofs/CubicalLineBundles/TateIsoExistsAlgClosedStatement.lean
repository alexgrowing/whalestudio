import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TateIsoExistsAlgClosed
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_exists_alg_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : PAT H (Sp K)) (I : TateIso D ℂ (Over.mk (spMap σ) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c))) (k : Type) [Field k] [IsAlgClosed k] (β : K →+* k), ∃ I' : TateIso D k (Over.mk (spMap β) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c)), (∀ (n : ℕ) (z : K), 0 < n → (I.ζ n : ℂ) = σ z → (I'.ζ n : k) = β z) ∧ ∀ (n : ℕ) a (s : 𝟙_ (Over (Sp K)) ⟶ T.t.G), 0 < n → toUnit _ ≫ s = I.ev n a → toUnit _ ≫ s = I'.ev n a := by
  first | exact @GlobalTheory.CM.tateIso_move | exact GlobalTheory.CM.tateIso_move | (intros; apply GlobalTheory.CM.tateIso_move <;> assumption)
