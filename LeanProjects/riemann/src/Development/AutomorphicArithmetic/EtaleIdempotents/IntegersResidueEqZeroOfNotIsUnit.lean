import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

theorem UpperTheory.integersResidue_eq_zero_of_not_isUnit :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (ϖ : OK l K), ¬ IsUnit ϖ → gRes r ϖ = 0 := by
  intro l _ K r ϖ hϖ
  have hu0 : (PreTilt.untilt (0 : Ob l) : OC l) = 0 := by
    rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
  have hnorm : ∀ x : OK l K, ‖((okToOC l K x : OC l) : ℂ_[l])‖ = ‖((x : K) : PadicAlgCl l)‖ :=
    fun x => norm_clToC _
  have hker : ∀ z : OK l K, r.ρ z = 0 → ‖((z : K) : PadicAlgCl l)‖ < 1 := fun z hz => by
    have h := r.hs z
    rw [hz, map_zero, hu0, zero_sub] at h
    have e : ((-(okToOC l K z) : OC l) : ℂ_[l]) = -((okToOC l K z : OC l) : ℂ_[l]) := rfl
    rw [e, norm_neg, hnorm] at h
    exact h
  have hρ : r.ρ ϖ = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := r.surj (r.ρ ϖ)⁻¹
    have hz : r.ρ (1 - ϖ * y) = 0 := by
      rw [map_sub, map_one, map_mul, hy, mul_inv_cancel₀ hne, sub_self]
    have h1 := hker _ hz
    have hsum : ((ϖ * y : OK l K) : K) = 1 - ((1 - ϖ * y : OK l K) : K) := by
      push_cast; ring
    have hlt : ‖(((ϖ * y : OK l K) : K) : PadicAlgCl l)‖ = 1 := by
      have e : (((ϖ * y : OK l K) : K) : PadicAlgCl l) = 1 - (((1 - ϖ * y : OK l K) : K) : PadicAlgCl l) := by
        rw [hsum]; push_cast; rfl
      refine le_antisymm (by simpa using norm_OK_le (ϖ * y)) ?_
      have h4 : ‖(1 : PadicAlgCl l)‖ ≤ max ‖(((ϖ * y : OK l K) : K) : PadicAlgCl l)‖ ‖(((1 - ϖ * y : OK l K) : K) : PadicAlgCl l)‖ := by
        have e' : (1 : PadicAlgCl l) = (((ϖ * y : OK l K) : K) : PadicAlgCl l) + (((1 - ϖ * y : OK l K) : K) : PadicAlgCl l) := by
          rw [e]; ring
        conv_lhs => rw [e']
        exact IsUltrametricDist.norm_add_le_max _ _
      rw [norm_one] at h4
      rcases le_max_iff.1 h4 with h5 | h5
      · exact h5
      · exact absurd h5 (not_le.2 h1)
    have hmul : ‖((ϖ : K) : PadicAlgCl l)‖ * ‖((y : K) : PadicAlgCl l)‖ = 1 := by
      rw [← norm_mul]; simpa using hlt
    have h2 := norm_OK_le ϖ
    have h3 := norm_OK_le y
    apply hϖ
    rw [isUnit_OK_iff]
    nlinarith [norm_nonneg ((ϖ : K) : PadicAlgCl l), norm_nonneg ((y : K) : PadicAlgCl l)]
  show Ideal.Quotient.mk _ (r.s (r.ρ ϖ)) = 0
  rw [hρ, map_zero, map_zero]
