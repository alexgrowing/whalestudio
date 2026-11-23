import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationUniqueOfPairingInjective
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
theorem _root_.GlobalTheory.T.polarization_unique_of_pairing_injective : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ φ : GG ⟶ GG.dual, (∀ ψ ψ' : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ (tau tw I y))) n = muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ' (tau tw I y))) n) → ψ = ψ') → (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → ∀ a : 𝓞 E, (tw.act t.act a : GG ⟶ GG) ≫ φ = φ ≫ dualHom GG GG (tw.act t.act (H.bar a)) := by
  first | exact @GlobalTheory.GroupBplus.Closed.act_comp_pol_eq | exact GlobalTheory.GroupBplus.Closed.act_comp_pol_eq | (intros; apply GlobalTheory.GroupBplus.Closed.act_comp_pol_eq <;> assumption)
