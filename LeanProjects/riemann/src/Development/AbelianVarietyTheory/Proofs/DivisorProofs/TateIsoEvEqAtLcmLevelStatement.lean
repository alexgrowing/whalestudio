import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_ev_eq_at_lcm_level : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
  (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
  (∀ a, J.ev l.A a = J'.ev l.A a) →
  (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
  ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  first | exact @GlobalTheory.LowDat.tateIso_ev_lcm_eq | exact GlobalTheory.LowDat.tateIso_ev_lcm_eq | (intros; apply GlobalTheory.LowDat.tateIso_ev_lcm_eq <;> assumption)
