import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutComponentSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutZeroNotLeSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutNonemptySt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutDimLowerSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u w

theorem CutComponent.proof (hZ : CutZeroNotLe.Statement.{u, w}) (hE : CutNonempty.Statement.{u, w})
    (hD : CutDimLower.Statement.{u, w}) : CutComponent.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hI
  obtain ⟨qq, hq, j, hj⟩ := hE k Ω N x n pp L s hW hL hs hI
  obtain ⟨f, hfZ, hfp⟩ := hZ k Ω N x (n + 1) pp L s hW hs hI
  have hlo := hD k Ω N x n pp L s qq hW hs hq ⟨j, hj⟩
  have hJq : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hq.1.2
  have hqp : qq.IsPrime := hq.1.1
  have hppq : pp ≤ qq := le_sup_left.trans hJq
  have := hW.isPrime

  have hpH : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    intro i r hr
    have := hW.homog r hr i
    rwa [← decomposition.decompose'_apply] at this
  have hZH : (zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ (by rintro f ⟨c, hc, -⟩; exact ⟨c, hc⟩)
  have hJH : (pp ⊔ zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    have h := (HomogeneousIdeal.toIdeal_sup ⟨pp, hpH⟩ ⟨_, hZH⟩).symm ▸
      (⟨pp, hpH⟩ ⊔ ⟨_, hZH⟩ : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous
    exact h

  have hcore : qq ≤ (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
    refine hq.2 ⟨hqp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    rw [← hJH.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJq
  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := by
    intro p hp d
    have := (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous d (hcore hp)
    have h2 : homogeneousComponent d p ∈
        (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
      rw [← decomposition.decompose'_apply]
      exact this
    exact Ideal.toIdeal_homogeneousCore_le _ _ h2

  have hup : ringKrullDim (Poly k N ⧸ qq) + 1 ≤ ((n + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hW.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hppq)
      (Ideal.Quotient.factor_surjective hppq) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hJq (Ideal.mem_sup_right hfZ)
  refine ⟨qq, hq, hqp, hhom, hW.le.trans hppq, ⟨j, hj⟩, ?_⟩

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize ringKrullDim (Poly k N ⧸ qq) = D at hup hlo ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hlo (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe m =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have h1 : n + 1 ≤ m := by exact_mod_cast hlo
      have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have h3 := Nat.cast_le.mp h2
      have : m = n + 1 := by omega
      subst this
      rfl

end GroundTheory.Heights₂.Heights.Kleiman
