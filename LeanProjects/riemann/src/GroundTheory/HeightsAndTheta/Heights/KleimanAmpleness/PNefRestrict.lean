import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_single (L : SubSystem S x Ω) (T : Finset (Fin 1)) :
    tensorSub ![L] T = if (0 : Fin 1) ∈ T then L else twistSys S x 0 := by
  have hf : List.finRange 1 = [0] := rfl
  split_ifs with h
  · simp [tensorSub, hf, h, twistSys_zero_twist]
  · simp [tensorSub, hf, h]

end Helpers

theorem NefRestrict.proof (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle M M' r hr hnef pp _ hpp
  have hx : IsSubvar x pp 1 := ⟨hpp.isPrime, hpp.homog, hle.trans hpp.le, hpp.relevant, hpp.dim⟩
  obtain ⟨r₀, hr₀⟩ := hRT.1 k Ω N x K' y hxy hle 0
  have hM := hRL k Ω N x K' y hxy hle pp 1 hpp M M' r hr
  have hO := hRL k Ω N x K' y hxy hle pp 1 hpp (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have heq : interSum pp ![M'.toSubSystem] =ᶠ[atTop] interSum pp ![M.toSubSystem] := by
    filter_upwards [hM, hO] with c hMc hOc
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_single, tensorSub_single]
    split_ifs
    · rw [hMc]
    · exact congrArg _ hOc
  have hnum : interNum pp ![M'.toSubSystem] = interNum pp ![M.toSubSystem] := by
    unfold interNum limUnder
    rw [Filter.map_congr heq]
  rw [hnum]
  exact hnef pp bot_le hx

end

end GroundTheory.Heights₂.Heights.Kleiman
