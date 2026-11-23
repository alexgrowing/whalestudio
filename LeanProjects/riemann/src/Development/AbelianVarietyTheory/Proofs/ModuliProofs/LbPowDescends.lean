import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropic

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LinDescent

open ThetaSplit in

theorem lbPow_descends : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) := by
  intro hlaw k _ _ P n C B _ ψ hn hnk htor hW hψ hfin het hsurj hker
  have := P.isAb.comm
  letI : CommGroup C := { (inferInstance : Group C) with mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }
  have hfinT : Finite {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} := by
    have h := (hlaw.mulN (Sp k) P n hn).2.2.2.2 k (𝟙 _) hnk
    exact Nat.finite_of_card_ne_zero (h.trans_ne (pow_ne_zero _ hn.ne'))
  have : Finite C := Finite.of_injective
    (fun c : C => (⟨c.1, htor c.1 c.2⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1}))
    fun a b h => Subtype.ext (congrArg (fun q => q.1) h)
  obtain ⟨u, hu, hc⟩ := exists_cocycle hlaw.globalFns P.isAb P.isLB (units_divisible k) n C.subtype
    (fun c c' => hW c.1 c.2 c'.1 c'.2)
  refine exists_descent_of_isReduced (Sp k) P.A B ψ C C.subtype (lbPow P.L n) (DVR.linComb_isLB P.L P.isLB _ _) hψ hfin het hsurj
    (fun k' _ _ t => ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c h => ?_⟩) u hu hc
  · obtain ⟨c, h₁, h₂⟩ := exists_rational_ker ψ t x hx
    exact ⟨⟨c, (hker c).1 h₁⟩, h₂⟩
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, (hker (C.subtype c)).2 c.2, MonObj.comp_one]
  · have : Epi t := epi_of_fields t
    refine Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 ?_))
    have e : toUnit (Over.mk t) ≫ c.1 = toUnit (Over.mk t) ≫ (1 : 𝟙_ (Over (Sp k)) ⟶ P.A) :=
      h.trans (MonObj.comp_one _).symm
    exact congrArg (fun q => q.left) e

end GlobalTheory.LinDescent
