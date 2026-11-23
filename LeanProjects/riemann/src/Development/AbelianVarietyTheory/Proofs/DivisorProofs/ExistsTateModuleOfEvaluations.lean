import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem tateLift_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)), (∀ k a b, ev k (a + b) = ev k a * ev k b) →
    (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) →
    (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) → (∀ a, ev 1 a = 1) →
    ∃ tι : Dw.La →+ P.T, (∀ a k, (tι a).lev k = ev (p ^ k) a) ∧ ∀ (o : 𝓞 E) a, tι (o • a) = P.actT o (tι a) := by
  intro E _ _ _ H Dw p _ _ P ev hadd hact htow hone
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : ∀ a k, ev (p ^ k) a ^ p ^ k = 1 := fun a k => by
    have := htow 1 (p ^ k) one_pos (pow_pos hp k) a
    rwa [Nat.one_mul, hone] at this
  have h2 : ∀ a k, ev (p ^ (k + 1)) a ^ p = ev (p ^ k) a := fun a k => by
    rw [pow_succ]
    exact htow (p ^ k) p (pow_pos hp k) hp a
  let f : Dw.La → P.T := fun a => Tate.mk (fun k => ev (p ^ k) a) fun k => ⟨h1 a k, h2 a k⟩
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, fun a k => rfl, ?_⟩
  · refine Tate.ext fun n => ?_
    have := hadd (p ^ n) 0 0
    rw [add_zero] at this
    change ev (p ^ n) 0 = 1
    exact left_eq_mul.1 this
  · intro a b
    exact Tate.ext fun n => hadd (p ^ n) a b
  · intro o a
    exact Tate.ext fun n => hact (p ^ n) o a

end GlobalTheory.FlatModel
