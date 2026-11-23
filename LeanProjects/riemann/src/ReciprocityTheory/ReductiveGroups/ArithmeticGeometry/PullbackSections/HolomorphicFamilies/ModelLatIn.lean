import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExistsSmallMemIdeal
import Formalism.FrobeniusOrbits.HostCorollaries

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open scoped Pointwise

theorem absNorm_smul_eq {E : Type} [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv _ _ σ)
    (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv).symm

theorem halfDiffNorm : HalfDiffNormSt := by
  intro D
  obtain ⟨hspec, -⟩ := D.host.𝔟_spec

  have hN : Ideal.absNorm (differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E)) =
      Ideal.absNorm D.host.𝔟 ^ 2 := by
    rw [hspec, map_mul, absNorm_smul_eq, sq]

  have htow := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ↥D.host.K) (𝓞 D.host.E)
  have hne : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hdisc : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) = (discr D.host.E).natAbs :=
    NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)
  have hrel0 : differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E) ≠ ⊥ := by
    intro h
    apply hne
    rw [htow, h]
    simp
  have hle : Ideal.absNorm (differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E)) ≤ (discr D.host.E).natAbs := by
    rw [← hdisc, htow, map_mul]
    apply Nat.le_mul_of_pos_right
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    intro h
    apply hne
    rw [htow, h]
    simp
  have hpos2 : 0 < Ideal.absNorm D.host.𝔟 ^ 2 := by
    rw [← hN, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hrel0
  have hpos : 0 < Ideal.absNorm D.host.𝔟 := pos_of_ne_zero fun h => by simp [h] at hpos2
  refine ⟨hpos, ?_⟩
  have hsq : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hN ▸ hle
  have hlog := Real.log_pow ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) 2
  push_cast at hlog
  rw [← hlog]
  exact Real.log_le_log (by positivity) hsq

theorem bb_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h0 := (halfDiffNorm D).1
  rw [h, Ideal.absNorm_bot] at h0
  exact lt_irrefl 0 h0

theorem absNorm_bb_sq_le (D : D7) : Ideal.absNorm D.host.𝔟 ^ 2 ≤ (discr D.host.E).natAbs := by
  obtain ⟨h0, hl⟩ := halfDiffNorm D
  have hd : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero D.host.E
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.𝔟 : ℝ) := by exact_mod_cast h0
  have key : (Ideal.absNorm D.host.𝔟 : ℝ) ^ 2 ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    rw [← Real.log_le_log_iff (by positivity) hd, Real.log_pow]
    push_cast
    linarith
  have h2 : ((discr D.host.E).natAbs : ℝ) = |((discr D.host.E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h3 : ((Ideal.absNorm D.host.𝔟 ^ 2 : ℕ) : ℝ) ≤ ((discr D.host.E).natAbs : ℝ) := by
    rw [h2]
    push_cast
    exact key
  exact_mod_cast h3

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n, Formalism.HC.Frame.GG, Nat.card_prod]
  have h2 : Nat.card ℤˣ = 2 := by
    first
      | rw [Nat.card_eq_fintype_card, Int.card_units_eq_two]
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
  have hA : Nat.card D.R.MA = D.R.ord := by
    unfold Formalism.HC.Frame.MA
    rw [Nat.card_congr Multiplicative.toAdd]
    unfold Formalism.HC.Frame.A Formalism.HC.Idx
    exact Nat.card_fin _
  rw [h2, hA]
  ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI
