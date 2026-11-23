import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

theorem bidual_comp_dualHom_eq_neg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ φ : GG ⟶ GG.dual, (∀ ψ ψ' : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ (tau tw I y))) n = muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ' (tau tw I y))) n) → ψ = ψ') → (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → GG.bidual.hom ≫ dualHom GG GG.dual φ = -φ := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I φ hext hφ
  apply hext
  intro x y n
  have hskew : Dw.EF y x = -Dw.EF x y := by
    have h := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt x, Dw.alt y, zero_add, add_zero] at h
    omega
  have hL : pairing GG k (tau tw I x) (tateMap GG GG.dual k (GG.bidual.hom ≫ dualHom GG GG.dual φ) (tau tw I y))
      = pairing GG k (tau tw I y) (tateMap GG GG.dual k φ (tau tw I x)) := by
    rw [tateMap_comp, ← pairing_tateMap]
    exact GlobalTheory.PerfdLat.pairing_bidual GG (tau tw I y) _
  have hR : pairing GG k (tau tw I x) (tateMap GG GG.dual k (-φ) (tau tw I y))
      = -pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y)) := by
    rw [map_neg, LinearMap.neg_apply, map_neg]
  rw [hL, hR, hφ y x n]
  have hinv : ∀ z : (mu p k).TateOver k, muRoot (-z) n * muRoot z n = 1 := fun z => by
    rw [← muRoot_add, neg_add_cancel, muRoot_zero]
  have h1 := hinv (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y)))
  rw [hφ x y n] at h1
  rw [hskew, zpow_neg, Units.val_inv_eq_inv_val]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end GlobalTheory.GroupBplus.Closed
