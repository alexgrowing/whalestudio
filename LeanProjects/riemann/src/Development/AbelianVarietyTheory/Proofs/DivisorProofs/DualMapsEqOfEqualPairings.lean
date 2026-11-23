import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k]
  {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k}

theorem latPt_surjective_base (tw : GG.TorsionTower t.G) (I : GeomTate Dw t) (n : ℕ) :
    Function.Surjective (latPt tw I n) := fun z => by
  have hz : (selfIso.inv ≫ spOver z ≫ tw.y n) ^ p ^ n = 1 := by
    rw [← MonObj.comp_pow, (tw.exists_iff n _).1 ⟨z, rfl⟩, MonObj.comp_one]
  obtain ⟨x, hx⟩ := (I.onto (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) _).1 hz
  refine ⟨x, tw.inj n k _ _ ?_⟩
  rw [latPt_y, hx, Iso.hom_inv_id_assoc]

theorem eq_of_forall_latPt [IsAlgClosed k] [CharZero k] (tw : GG.TorsionTower t.G) (I : GeomTate Dw t) (n : ℕ)
    {a b : GG.A n} (h : ∀ x, latPt tw I n x a = latPt tw I n x b) : a = b :=
  TateFree.eq_of_forall_pts k k (GG.A n) fun z => by
    obtain ⟨x, rfl⟩ := latPt_surjective_base tw I n z
    exact h x

theorem hom_dual_ext_of_pairing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ φ ψ : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k ψ (tau tw I y))) n) → φ = ψ := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I φ ψ h
  refine PDivGroup.hom_ext fun n => BialgHom.ext fun f => eq_of_forall_latPt tw I n fun y => ?_
  have hc : charElem (tateMap GG GG.dual k φ (tau tw I y)) n =
      charElem (tateMap GG GG.dual k ψ (tau tw I y)) n :=
    eq_of_forall_latPt tw I n fun x => by
      have := h x y n
      rwa [muRoot_pairing, muRoot_pairing] at this
  have h1 := apply_charElem (tateMap GG GG.dual k φ (tau tw I y)) n f
  have h2 := apply_charElem (tateMap GG GG.dual k ψ (tau tw I y)) n f
  rw [hc, h2] at h1
  exact h1.symm

end GlobalTheory.GroupBplus.Closed
