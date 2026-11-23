import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TatePointSurjectiveOnFiniteLevel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_point_surjective_on_finite_level : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ (n : ℕ) (K : Type) [Field K] [Algebra k K] (φ : GG.A n →ₐ[k] K), ∃ x : Dw.La, tatePt (tau tw I x) n K = φ := by
  first | exact @GlobalTheory.GroupBplus.Closed.tatePt_tau_surjective | exact GlobalTheory.GroupBplus.Closed.tatePt_tau_surjective | (intros; apply GlobalTheory.GroupBplus.Closed.tatePt_tau_surjective <;> assumption)
