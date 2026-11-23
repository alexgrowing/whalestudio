import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfB

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem unit_comp (w : (LetA O n)ˣ) (i : ZMod n) :
    (w : LetA O n) i * ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i = 1 := by
  exact congrFun (Units.mul_inv w) i

theorem π_at (s' : ℕ) (π' : LetA O n) (w₁ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (i : ZMod n) :
    π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := by
  rw [hπ]
  rfl

theorem hlet_of [IsDomain O] (s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n) (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hπΔ : π' ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (c : ZMod n) :
    ∀ a : O, a ≠ 0 → ∀ u : W.EE,
      (∃ g ∈ W.AΔ, algebraMap (LetA O n) W.EE π' * u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      (∃ g ∈ W.AΔ, a • u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      ∃ g ∈ W.AΔ, u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by
  rintro a ha u ⟨g, hg, hgu⟩ ⟨h, hh, hhu⟩
  have hA : π' * ((letE c : LetA O n) * h) = algebraMap O (LetA O n) a * ((letE c : LetA O n) * g) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (π' * ((letE c : LetA O n) * h))
        = algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * h) := map_mul _ _ _
      _ = algebraMap (LetA O n) W.EE π' * (a • u) := by rw [hhu]
      _ = a • (algebraMap (LetA O n) W.EE π' * u) := by rw [mul_smul_comm]
      _ = a • algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by rw [hgu]
      _ = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) a * ((letE c : LetA O n) * g)) := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
  have hc : π' c * h c = a • g c := by
    have := congrFun hA c
    rw [Algebra.smul_def]
    simpa [letE] using this
  have hdvd : PowerSeries.X ^ s' ∣ g c := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have h1 := congrArg (PowerSeries.coeff m) hc
    rw [π_at s' π' w₁ hπ c, mul_comm ((w₁ : LetA O n) c), mul_assoc, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega), map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left ha
  obtain ⟨G', hG'⟩ := hdvd
  set g' : LetA O n := (letE c : LetA O n) * (fun _ => ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c * G') with hg'
  have hπg' : π' * g' = (letE c : LetA O n) * g := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.mul_apply, hg', letE, Pi.single_eq_same, one_mul]
      rw [π_at s' π' w₁ hπ i, hG']
      linear_combination (PowerSeries.X ^ s' * G') * unit_comp w₁ i
    · simp [hg', letE, Pi.single_apply, hi]
  have hcancel : ∀ x y : LetA O n, π' * x = π' * y → x = y := by
    intro x y hxy
    funext i
    have hxi := congrFun hxy i
    simp only [Pi.mul_apply] at hxi
    rw [π_at s' π' w₁ hπ i] at hxi
    have hne : (w₁ : LetA O n) i * PowerSeries.X ^ s' ≠ 0 := by
      have hw : (w₁ : LetA O n) i ≠ 0 := by
        intro h0
        have := unit_comp w₁ i
        rw [h0, zero_mul] at this
        exact zero_ne_one this
      exact mul_ne_zero hw (pow_ne_zero _ PowerSeries.X_ne_zero)
    exact mul_left_cancel₀ hne hxi
  have hπΔ' : ∀ δ ∈ W.DelF, W.γA δ π' = π' := hπΔ
  have hm : (letE c : LetA O n) * g ∈ W.AΔ := mul_mem (letE_mem W c) hg
  have hm' : ∀ δ ∈ W.DelF, W.γA δ ((letE c : LetA O n) * g) = (letE c : LetA O n) * g := hm
  have hg'Δ : g' ∈ W.AΔ := by
    show ∀ δ ∈ W.DelF, W.γA δ g' = g'
    intro δ hδ
    apply hcancel
    calc π' * W.γA δ g' = W.γA δ π' * W.γA δ g' := by rw [hπΔ' δ hδ]
      _ = W.γA δ (π' * g') := (map_mul _ _ _).symm
      _ = W.γA δ ((letE c : LetA O n) * g) := by rw [hπg']
      _ = (letE c : LetA O n) * g := hm' δ hδ
      _ = π' * g' := hπg'.symm
  refine ⟨g', hg'Δ, ?_⟩
  have hle : (letE c : LetA O n) * g' = g' := by rw [hg', ← mul_assoc, letE_mul_self']
  rw [hle]
  exact hπu.mul_left_cancel (by rw [hgu, ← hπg', map_mul])

theorem q_unit (hp : PD.p.Prime) : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  exact Formalism.MainNotions.LiftingTheory.liftb_q_unit W

end Formalism.MainNotions.N.Ln34.MQ
