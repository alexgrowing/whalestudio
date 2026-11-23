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

namespace GlobalTheory.GroupBplus.Closed

theorem tateMap_act_tau_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type}
    [Field k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G)
    (I : GeomTate Dw t) (a : 𝓞 E) (y : Dw.La) :
    tateMap GG GG k (tw.act t.act a : GG ⟶ GG) (tau tw I y) = tau tw I (a • y) := by
  have := t.act.hom a
  refine TateOver.ext (funext fun n => ?_)
  refine tw.inj n k _ _ ?_
  have e : (tateMap GG GG k (tw.act t.act a : GG ⟶ GG) (tau tw I y)).pt n =
      (latPt tw I n y).comp ((tw.map tw (t.act.act a)).app n : GG.A n →ₐ[k] GG.A n) :=
    AlgHom.ext fun _ => rfl
  rw [e, tau_pt, ← spOver_comp, Category.assoc, tw.map_y, ← Category.assoc, latPt_y, latPt_y, I.lin, Category.assoc]

theorem act_comp_pol_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ φ : GG ⟶ GG.dual, (∀ ψ ψ' : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ (tau tw I y))) n = muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ' (tau tw I y))) n) → ψ = ψ') → (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → ∀ a : 𝓞 E, (tw.act t.act a : GG ⟶ GG) ≫ φ = φ ≫ dualHom GG GG (tw.act t.act (H.bar a)) := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I φ hext hφ a
  have hb : H.bar (H.bar a) = a := RingOfIntegers.ext (by
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  refine hext _ _ fun x y n => ?_
  rw [tateMap_comp, tateMap_comp]
  have h1 := pairing_tateMap (B := k) (tw.act t.act (H.bar a) : GG ⟶ GG) (tau tw I x)
    (tateMap GG GG.dual k φ (tau tw I y))
  rw [tateMap_act_tau_adj] at h1
  rw [tateMap_act_tau_adj, hφ]
  refine Eq.trans ?_ (congrArg (muRoot · n) h1)
  rw [hφ, Dw.adj, hb]

end GlobalTheory.GroupBplus.Closed
