import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem labels_of_tateIsoQ : BrGtSt → BrWpSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ n a, ν.QPt (I.ev n a) (q n a)) → Labels N D.EF I.ζ q ∧ ∀ k, 0 < k → ∀ (x : 𝓞 E) (a : D.La), ∃ z, ν.eX (q k (x • a)).1.1.toAdd = x • ν.eX (q k a).1.1.toAdd + k • z := by
  intro hG hW E _ _ _ H D R _ _ D₀ _ oa he hB F _ _ _ I N ν q hq
  obtain ⟨h1, -, h2, -, hQ⟩ := hG R D₀ he hB F N ν
  obtain ⟨hadd, htow⟩ := GlobalTheory.NestQVal.qval_add_tower E H D R D₀ oa he hB F I N ν q h1 h2
    (fun k => ⟨(hQ k).1, (hQ k).2.2⟩) hq
  refine ⟨⟨hadd, fun n hn a b => ?_, fun n hn p => ?_, htow, fun n hn a b => ?_⟩, fun n hn x a => ?_⟩
  · rw [← (hQ n).2.2 _ _ _ _ (hq n a) (hq n b)]
    exact I.ker n hn a b
  · obtain ⟨p₀, hp₀⟩ := (hQ n).2.1 p
    obtain ⟨a, ha⟩ := I.onto n hn p₀
    exact ⟨a, ((hQ n).2.2 _ _ _ _ (hq n a) hp₀).1 ha⟩
  · exact Units.ext ((hW R D₀ he hB F N ν n hn _ _ _ _ _ (hq n a) (hq n b)).1 (I.isom n hn a b)).symm
  · obtain ⟨q₀, hy, -, heq⟩ := I.lin n hn x a
    obtain ⟨c, hc, -⟩ := (hQ n).1 q₀
    obtain ⟨z, hz, -⟩ := ((hQ n).2.2 _ _ _ _ hc (hq n (x • a))).1 heq
    exact ⟨ν.eX z, by rw [hz, map_add, map_nsmul, hc.1, hy, (hq n a).1]⟩

end GlobalTheory.ModelData
