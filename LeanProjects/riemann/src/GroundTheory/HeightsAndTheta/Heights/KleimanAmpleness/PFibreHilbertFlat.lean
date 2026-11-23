import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreHilbertFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsFibreSectionsFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExtendTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem interSum_single_eq {R : Type*} [CommRing R] {Ω : Type w} [Field Ω] [Algebra R Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (pp : Ideal (Poly R N)) (L : SubSystem R x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys R x (c : ℤ))) - restrLen pp (twistSys R x (c : ℤ)) := by
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have h0 : tensorSub ![L] ∅ = twistSys R x 0 := rfl
  have h1 : tensorSub ![L] {0} = (twistSys R x 0).twist L := rfl
  rw [interSum, huniv, Finset.sum_pair (by decide), h0, h1, twistSys_zero_twist, twistSys_zero_twist]
  simp only [Finset.card_empty, Finset.card_singleton, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero]
  ring

theorem FibreHilbertFlat.proof (h : FibreSectionsFlat.Statement.{u, w}) : FibreHilbertFlat.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 qq hq hconst hsub
  have hM := h S F Ω N x M 𝔪 h𝔪 qq hq hconst 1 hsub
  have hO := h S F Ω N x (twistBundle S x 0) 𝔪 h𝔪 qq hq hconst 1 hsub
  filter_upwards [hM, hO] with c eM eO
  have hO0 : (twistBundle S x 0).toSubSystem = twistSys S x 0 := rfl
  rw [hO0, SubSystem.extend_twistSys, twistSys_zero_twist, twistSys_zero_twist] at eO
  rw [interSum_single_eq, interSum_single_eq, eM, eO]

end

end GroundTheory.Heights₂.Heights.Kleiman
