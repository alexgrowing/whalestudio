import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (pullDeg baseDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

section Twist

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

theorem zpow_mem_subalgebra_of_inv_mem (A : Subalgebra S Ω) {u : Ω} (hu : u ∈ A) (hu' : u⁻¹ ∈ A) (n : ℤ) :
    u ^ n ∈ A := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_mem hu m
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem hu' m

theorem prod_segreChart_twist (d c : ∀ k, ι k) (β : K → ℤ) (n : ℤ) :
    ∏ k, segreJoin y ⟨k, segreChart d c k⟩ ^ (-(pullDeg β + n • baseDeg (Sum.inl ()) : Unit ⊕ K → ℤ) k) =
      segreVec y d ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  rw [Fintype.prod_sum_type]
  simp [pullDeg, baseDeg]
  rfl

omit [DecidableEq K] in

theorem prod_add_const (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (β : K → ℤ) (n : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(β + fun _ => n : K → ℤ) k) = segreVec y c ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-(β + fun _ => n : K → ℤ) k) = y ⟨k, c k⟩ ^ (-n) * y ⟨k, c k⟩ ^ (-β k) := fun k => by
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k), mul_comm]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_zpow]
  rfl

theorem secOver_segreJoin_twist (β : K → ℤ) (n : ℤ) :
    secOver S (segreJoin y) (pullDeg β + n • baseDeg (Sum.inl ())) = secOver S y (β + fun _ => n) := by
  ext s
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c hc
    have := h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)
    rw [prod_segreChart_twist] at this
    rw [prod_add_const y c hc]
    exact segre_diag_le y c this
  · intro h C hC
    obtain ⟨d, c, rfl⟩ := segreChart_eta C
    have hd : segreVec y d ≠ 0 := hC (Sum.inl ())
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hC (Sum.inr k)
    have hc0 : segreVec y c ≠ 0 := segreVec_ne_zero y hc
    have hs := chartRingOver_le_segre y d c (h c hc)
    rw [prod_add_const y c hc] at hs
    set R := chartRingOver S (segreJoin y) (segreChart d c)
    have hu : segreVec y c / segreVec y d ∈ R := Algebra.subset_adjoin ⟨⟨Sum.inl (), c⟩, rfl⟩
    have hu' : (segreVec y c / segreVec y d)⁻¹ ∈ R := by
      rw [inv_div]
      exact chartRingOver_le_segre y d c (segreVec_div_mem y c d)
    have e : s * (segreVec y d ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k)) =
        s * (segreVec y c ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (segreVec y c / segreVec y d) ^ n := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [prod_segreChart_twist, e]
    exact mul_mem hs (zpow_mem_subalgebra_of_inv_mem R hu hu' n)

end Twist

theorem SegreTwist.proof : SegreTwist.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y _ β c
  exact secOver_segreJoin_twist y β c

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
