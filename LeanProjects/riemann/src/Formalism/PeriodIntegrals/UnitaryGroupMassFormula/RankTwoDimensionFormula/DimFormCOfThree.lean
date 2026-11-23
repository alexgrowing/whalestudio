import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfSteps

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitCount : OrbitCount := by
  intro G _ Γ K n t A N hA hAN hK hΓ
  classical
  have key : ∀ j i, DoubleCoset.mk Γ K (t i) = DoubleCoset.mk Γ K (t j) →
      ∃ γ ∈ Γ, ∃ κ ∈ K, t j = γ * t i * κ := fun j i h => (DoubleCoset.eq Γ K (t i) (t j)).mp h
  have hcard : (Finset.univ : Finset (Fin n)).card ≤
      N * (Finset.univ.image fun i => DoubleCoset.mk Γ K (t i)).card := by
    apply Finset.card_le_mul_card_image
    intro a ha
    obtain ⟨i0, -, rfl⟩ := Finset.mem_image.mp ha
    let g : Fin n → G := fun j =>
      if h : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) then (key j i0 h).choose else 1
    calc (Finset.univ.filter fun j => DoubleCoset.mk Γ K (t j) = DoubleCoset.mk Γ K (t i0)).card
        ≤ hA.toFinset.card := by
          apply Finset.card_le_card_of_injOn g
          · intro j hj
            have hj' : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2).symm
            obtain ⟨hγ, κ, hκ, he⟩ := (key j i0 hj').choose_spec
            rw [Finset.mem_coe, Set.Finite.mem_toFinset]
            simp only [g, dif_pos hj']
            exact hΓ i0 j _ hγ κ hκ he
          · intro j hj j' hj' hgg
            have h1 : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j) :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2).symm
            have h2 : DoubleCoset.mk Γ K (t i0) = DoubleCoset.mk Γ K (t j') :=
              ((Finset.mem_filter.mp (Finset.mem_coe.mp hj')).2).symm
            obtain ⟨-, κ, hκ, he⟩ := (key j i0 h1).choose_spec
            obtain ⟨-, κ', hκ', he'⟩ := (key j' i0 h2).choose_spec
            simp only [g, dif_pos h1, dif_pos h2] at hgg
            apply hK
            rw [he, he', hgg]
            have e1 : ((key j' i0 h2).choose * t i0 * κ)⁻¹ * ((key j' i0 h2).choose * t i0 * κ') = κ⁻¹ * κ' := by
              group
            rw [e1]
            exact K.mul_mem (K.inv_mem hκ) hκ'
      _ ≤ N := by
          rw [← Set.ncard_eq_toFinset_card A hA, ← Nat.card_coe_set_eq]
          exact hAN
  have e : Nat.card (Set.range fun i => DoubleCoset.mk Γ K (t i)) =
      (Finset.univ.image fun i => DoubleCoset.mk Γ K (t i)).card := by
    first
      | rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_range]
      | simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  rw [e]
  simpa using hcard

theorem kuStab : KuStab := by
  intro D X u hK h κ
  obtain ⟨⟨κ, hκ'⟩, hκ⟩ := κ
  have hk : (X.xu u)⁻¹ * κ * X.xu u ∈ X.K2 := hκ
  show latS X u (h * κ) = latS X u h
  have h2 : ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ ∈ X.K2 := hK.2.2.1 _ hk
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.K2 K2set at h2
  have hs : ∀ x, x ∈ X.B.I.Lf ↔
      (X.B.I.fmat ((X.xu u)⁻¹ * κ * X.xu u)⁻¹).mulVec x ∈ X.B.I.Lf := h2.1
  have he : (h * κ * X.xu u)⁻¹ = ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * (h * X.xu u)⁻¹ := by
    group
  have hm : X.B.I.fmat (((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * (h * X.xu u)⁻¹) =
      X.B.I.fmat ((X.xu u)⁻¹ * κ * X.xu u)⁻¹ * X.B.I.fmat (h * X.xu u)⁻¹ := rfl
  ext y
  simp only [latS, Set.mem_setOf_eq]
  rw [he, hm, ← Matrix.mulVec_mulVec]
  exact (hs _).symm

theorem dimFormC_of_three (hT : Transport) (hB : StabBound) (hI : IndexGe) : Formalism.L2.SG.KappaOffDiagonal.DimFormC :=
  dimFormC_of_steps orbitCount hT kuStab hB hI

end PI.UnitaryDimensionFormula
