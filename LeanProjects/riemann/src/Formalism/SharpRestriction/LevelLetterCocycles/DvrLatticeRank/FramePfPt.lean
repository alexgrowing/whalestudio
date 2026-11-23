import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLoc

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Zero

open PowerSeries

variable {LL : Type} [Field LL]

theorem framepf_exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative LL E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  have hX1 : X ∣ E - 1 := by
    rw [PowerSeries.X_dvd_iff]
    simp [h0]
  obtain ⟨w1, hw1⟩ := hX1
  have hc1 : constantCoeff w1 = 1 := by
    have h2 : coeff 0 (PowerSeries.derivative LL E) = coeff 1 E := by
      rw [PowerSeries.coeff_derivative]
      simp
    rw [hd] at h2
    have h1 : coeff 1 (E - 1) = coeff 0 w1 := by
      rw [hw1]
      exact PowerSeries.coeff_succ_X_mul 0 w1
    have h3 : coeff 1 (E - 1) = coeff 1 E := by
      simp [PowerSeries.coeff_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1, h3, ← h2,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  induction p with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, hwc⟩ := ih
    refine ⟨w * E + w1, ?_, ?_⟩
    · have he : E ^ (k + 1) - 1 = (E ^ k - 1) * E + (E - 1) := by ring
      rw [he, hw, hw1]
      ring
    · simp [hwc, hc1, h0]

end Zero

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

open PowerSeries in

theorem framepf_lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  obtain ⟨w, hw, hwc⟩ := framepf_exp_pow_sub_one E hE0 hEd PD.p
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have h1 := W.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hp1 : PD.p ≠ 1 := by
    intro h
    have h1 := W.v_l
    rw [h, Nat.cast_one, AddValuation.map_one] at h1
    simp at h1
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h2 := hζ.eq_orderOf
    rw [h, orderOf_one] at h2
    exact hp1 h2
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hfq : W.lev c ζ letπ * W.lev c ζ W.q = E ^ PD.p - 1 := by
    rw [← map_mul, hq, map_sub, map_pow, map_add, map_one, hE, mul_pow, ← map_pow, hζp, map_one,
      one_mul]
  set P := W.lev c ζ letπ with hPdef
  have hP : P = C ζ * E - 1 := eq_sub_of_add_eq' hE
  have hPc : constantCoeff P = ζ - 1 := by
    rw [hP]
    simp [hE0]
  have hPne : constantCoeff P ≠ 0 := by
    rw [hPc]
    exact sub_ne_zero.mpr hζ1
  refine ⟨w * P⁻¹, ?_, ?_⟩
  · have hinv : P⁻¹ * P = 1 := PowerSeries.inv_mul_cancel P hPne
    calc W.lev c ζ W.q = (P⁻¹ * P) * W.lev c ζ W.q := by rw [hinv, one_mul]
      _ = P⁻¹ * (E ^ PD.p - 1) := by rw [mul_assoc, hfq]
      _ = X * (w * P⁻¹) := by rw [hw]; ring
  · rw [map_mul, hwc, PowerSeries.constantCoeff_inv, hPc]
    exact mul_ne_zero hp0 (inv_ne_zero (sub_ne_zero.mpr hζ1))

theorem framepf_Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [Formalism.BasicNotions.LocWach.Q, hs]

theorem framepf_Q_at (hs : W.s = 1) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := framepf_lev_q_simple W c ζ hζ
  rw [framepf_Q_eq_q W hs, hu]
  refine ⟨by simp, ?_⟩
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * u) = PowerSeries.coeff 0 u :=
    PowerSeries.coeff_succ_X_mul 0 u
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hu0

end Local

theorem framepf_pt_prim (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : IsPrimitiveRoot ζ l := by
  obtain ⟨τs, ⟨-, hroot⟩, -⟩ := hpt
  have hpow : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rwa [zero_add, (D.loc l).ζQ_zero] at h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show _ ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    refine (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ _) ?_
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one]
    exact hpow
  set y : Ks K 1 := ⟨_, hmem⟩ with hydef
  have hyζ : τs y = ζ := hroot y rfl
  have hy1 : y ^ l = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hpow
  have hy2 : y ≠ 1 := by
    intro h
    apply (D.loc l).ζQ_one
    have h' := congrArg Subtype.val h
    exact h'
  have hprim : IsPrimitiveRoot y l := by
    have ho := orderOf_eq_prime hy1 hy2
    have h0 := IsPrimitiveRoot.orderOf y
    rwa [ho] at h0
  rw [← hyζ]
  exact hprim.map_of_injective τs.injective

end Formalism.MainNotions.N.Ln34

end
