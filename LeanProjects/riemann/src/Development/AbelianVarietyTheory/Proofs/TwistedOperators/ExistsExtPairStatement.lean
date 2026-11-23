import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ext_pair_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  first | exact @GlobalTheory.HkIntegral.exists_ext_pair | exact GlobalTheory.HkIntegral.exists_ext_pair | (intros; apply GlobalTheory.HkIntegral.exists_ext_pair <;> assumption)
