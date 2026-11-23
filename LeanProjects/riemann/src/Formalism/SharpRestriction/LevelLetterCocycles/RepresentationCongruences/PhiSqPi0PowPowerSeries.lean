import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvOSmulO

open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

theorem ea_sub (a : ZMod n) (F F' : PowerSeries O) : ea Br a (F - F') = ea Br a F - ea Br a F' := by
  have h := ea_add Br a (F - F') F'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem ea_mul_algO (a : ZMod n) (F : PowerSeries O) (x : O) :
    ea Br a F * algebraMap O W.EE x = ea Br a (F * C x) := by
  rw [mul_comm F, ea_C_mul, mul_comm]

theorem ea_mul_cst (a : ZMod n) (F G : PowerSeries O) :
    ea Br a F * algebraMap (LetA O n) W.EE (Br.cst G) = ea Br a (F * G) := by
  rw [mul_comm, cst_mul_ea, mul_comm G]

theorem ea_def (a : ZMod n) (F : PowerSeries O) :
    ea Br a F = algebraMap (LetA O n) W.EE (letE a * 1 * Br.cst F) := by
  unfold ea; rw [mul_one]

theorem inFr_one_ea (a : ZMod n) (G F : PowerSeries O) :
    InFr W a 1 (Br.cst G) (ea Br a F) :=
  ⟨Br.cst (G * F), Br.cst_mem _, by rw [cst_mul_ea, ea_def]⟩

theorem inId_two (a : ZMod n) (α : ℕ → ℤ) (g : W.EE) :
    InId W a 2 α g ↔ InFr W a (Br.cst (X ^ (α 0).toNat * Br.P.p 1 ^ (α 1).toNat))
      (Br.cst (X ^ (-(α 0)).toNat * Br.P.p 1 ^ (-(α 1)).toNat)) g := by
  unfold InId
  rw [prod_two_levels_eq_const Br, prod_two_levels_eq_const Br]

theorem pi0_eq_cst_X_sub_C_prime : W.π₀ = Br.cst (X - C ((PD.p : ℕ) : O)) := Br.π₀_eq

theorem phi_sq_pi0_pow_power_series (h G : ℕ) :
    ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ 2) W.π₀) ^ N = W.π₀ * (Br.cst (X ^ h * Br.P.p 1 ^ G)) ^ 2 * w := by
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  have hl1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  set N := 2 * h + 2 * G + 1 with hN
  have hφ2 : (W.φA ^ 2) W.π₀ = Br.cst (Br.P.φ (Br.P.φ (X - C ((PD.p : ℕ) : O)))) := by
    rw [pow_two, AlgHom.mul_apply, pi0_eq_cst_X_sub_C_prime Br, Br.φA_cst, Br.φA_cst]
  have hφφ : Br.P.φ (Br.P.φ (X - C ((PD.p : ℕ) : O))) =
      Br.P.φ Br.P.u * Br.P.u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) * Br.P.p 1 ^ (PD.p - 1) := by
    rw [Br.P.hφ0, map_mul, map_mul, map_pow, Br.P.hφ0]
    have : Br.P.φ X = Br.P.p 1 := rfl
    rw [this]; ring
  have e1 : (PD.p - 1) * N = 2 * h + ((PD.p - 1) * N - 2 * h) := by
    have : 2 * h ≤ (PD.p - 1) * N := by nlinarith
    omega
  have e2 : (PD.p - 1) * N = 2 * G + ((PD.p - 1) * N - 2 * G) := by
    have : 2 * G ≤ (PD.p - 1) * N := by nlinarith
    omega
  have e3 : N = 1 + (N - 1) := by omega
  refine ⟨N, Br.cst ((Br.P.φ Br.P.u * Br.P.u) ^ N * (X - C ((PD.p : ℕ) : O)) ^ (N - 1) *
      X ^ ((PD.p - 1) * N - 2 * h) * Br.P.p 1 ^ ((PD.p - 1) * N - 2 * G)), Br.cst_mem _, ?_⟩
  rw [hφ2, hφφ, pi0_eq_cst_X_sub_C_prime Br, ← Br.cst_pow, ← Br.cst_pow, ← Br.cst_mul, ← Br.cst_mul]
  congr 1
  have : (Br.P.φ Br.P.u * Br.P.u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) * Br.P.p 1 ^ (PD.p - 1)) ^ N =
      (Br.P.φ Br.P.u * Br.P.u) ^ N * (X - C ((PD.p : ℕ) : O)) ^ N * X ^ ((PD.p - 1) * N) *
        Br.P.p 1 ^ ((PD.p - 1) * N) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  rw [this, show (X : PowerSeries O) ^ ((PD.p - 1) * N) = X ^ (2 * h) * X ^ ((PD.p - 1) * N - 2 * h) by
      rw [← pow_add, ← e1],
    show Br.P.p 1 ^ ((PD.p - 1) * N) = Br.P.p 1 ^ (2 * G) * Br.P.p 1 ^ ((PD.p - 1) * N - 2 * G) by
      rw [← pow_add, ← e2],
    show (X - C ((PD.p : ℕ) : O)) ^ N = (X - C ((PD.p : ℕ) : O)) * (X - C ((PD.p : ℕ) : O)) ^ (N - 1) by
      rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ N by omega)]]
  ring

theorem coeff_zero_of_coord (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (K h : ℕ)
    (Y D : PowerSeries O) (u : LetA O n) (hu : u ∈ W.AΔ)
    (hK : algebraMap (LetA O n) W.EE (letE a) * (lE W K * ea Br a D) =
      algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u)) :
    ∀ j < h, coeff j D = 0 := by
  obtain ⟨U, hU⟩ := letE_mul_AΔ Br a hu
  have e1 : algebraMap (LetA O n) W.EE (letE a) * (lE W K * ea Br a D) =
      ea Br a (C (((PD.p : ℕ) : O) ^ K) * D) := by
    rw [ea_C_mul]; unfold ea
    simp only [lE, map_pow, map_natCast]
    rw [show (algebraMap (LetA O n) W.EE) (letE a) * (((PD.p : ℕ) : W.EE) ^ K *
        (algebraMap (LetA O n) W.EE) (letE a * Br.cst D)) = ((PD.p : ℕ) : W.EE) ^ K *
        (algebraMap (LetA O n) W.EE) ((letE a * letE a) * Br.cst D) by rw [map_mul, map_mul, map_mul]; ring,
      letE_mul_self]
  have e2 : algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u) =
      ea Br a ((X - C ((PD.p : ℕ) : O)) * (X ^ h * Y) * U) := by
    unfold ea
    congr 1
    rw [show letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u = (W.π₀ * Br.cst (X ^ h * Y)) * (letE a * u) by ring, hU,
      pi0_eq_cst_X_sub_C_prime Br, Br.cst_mul ((X - C ((PD.p : ℕ) : O)) * (X ^ h * Y)) U,
      Br.cst_mul (X - C ((PD.p : ℕ) : O)) (X ^ h * Y)]
    ring
  rw [e1, e2] at hK
  have hD := ea_inj Br a hK
  intro j hj
  have h1 := congrArg (coeff j) hD
  rw [coeff_C_mul, show (X - C ((PD.p : ℕ) : O)) * (X ^ h * Y) * U = X ^ h * ((X - C ((PD.p : ℕ) : O)) * Y * U) by ring,
    coeff_X_pow_mul', if_neg (by omega)] at h1
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ Br.P.hl0)

theorem dvd_of_not_dvd {x y : O} (h : ¬ y ∣ x) : x ∣ y := by
  by_cases hx : x = 0
  · exact absurd (hx ▸ dvd_zero y) h
  by_cases hy : y = 0
  · exact hy ▸ dvd_zero x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rcases le_or_gt m m' with hm | hm
  · refine ⟨↑u⁻¹ * u' * ϖ ^ (m' - m), ?_⟩
    rw [show ϖ ^ m' = ϖ ^ m * ϖ ^ (m' - m) by rw [← pow_add, Nat.add_sub_cancel' hm]]
    have : (u : O) * ↑u⁻¹ = 1 := u.mul_inv
    linear_combination (-(↑u' * ϖ ^ m * ϖ ^ (m' - m))) * this
  · exfalso; apply h
    refine ⟨↑u'⁻¹ * u * ϖ ^ (m - m'), ?_⟩
    rw [show ϖ ^ m = ϖ ^ m' * ϖ ^ (m - m') by rw [← pow_add, Nat.add_sub_cancel' hm.le]]
    have : (u' : O) * ↑u'⁻¹ = 1 := u'.mul_inv
    linear_combination (-(↑u * ϖ ^ m' * ϖ ^ (m - m'))) * this

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
