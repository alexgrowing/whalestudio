import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOddLevelCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_odd_level_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) → ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i) (ω : ∀ i, R i →+* c.F) (n : I → ℕ), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧ ∀ i, 3 ≤ n i ∧ Odd (n i) ∧ n i ∣ l.M ∧ a i = (n i : 𝓞 c.F) := by
  first | exact @GlobalTheory.Member.exists_cover_of_goodAt_all | exact GlobalTheory.Member.exists_cover_of_goodAt_all | (intros; apply GlobalTheory.Member.exists_cover_of_goodAt_all <;> assumption)
