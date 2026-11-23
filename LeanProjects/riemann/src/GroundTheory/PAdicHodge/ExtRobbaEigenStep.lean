import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem convAll_π : T.ConvAll (algebraMap Γ T.B T.π) := by
  simpa using convAll_π_pow (T := T) 1

theorem convAll_invSelf : T.ConvAll (IsLocalization.Away.invSelf T.π) := fun ρ _ _ => by
  rw [coeffB_invSelf]; exact convergesAt_pi_single _ _ _

variable (T) in

def piE (σ : Set.Ioo (0 : ℝ) 1) : T.RobbaExt σ := T.ofAll _ convAll_π σ

variable (T) in

def piInvE (σ : Set.Ioo (0 : ℝ) 1) : T.RobbaExt σ := T.ofAll _ convAll_invSelf σ

theorem piE_mul_piInvE (σ : Set.Ioo (0 : ℝ) 1) : T.piE σ * T.piInvE σ = 1 := by
  have : algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π = 1 :=
    IsLocalization.Away.mul_invSelf T.π
  have h1 : T.ofAll _ (convAll_π.mul convAll_invSelf) σ = ((1 : T.Econ σ) : T.RobbaExt σ) := by
    rw [ofAll]; congr 1; exact Subtype.ext this
  rw [piE, piInvE, ← ofAll_mul, h1, Completion.coe_one]

theorem res_piE {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) : T.res h (T.piE ρ0) = T.piE ρ1 :=
  res_ofAll _ h

theorem res_piInvE {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    T.res h (T.piInvE ρ0) = T.piInvE ρ1 :=
  res_ofAll _ h

theorem extNorm_piE {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) : T.extNorm σ ρ (T.piE σ) = ρ := by
  rw [piE, extNorm_ofAll, coeffB_algebraMap, ← pow_one T.π, zcoeff_π_pow,
    gaussNorm_pi_single _ _ ρ.2.1]
  simp

theorem extNorm_piInvE {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) :
    T.extNorm σ ρ (T.piInvE σ) = (ρ : ℝ)⁻¹ := by
  rw [piInvE, extNorm_ofAll, coeffB_invSelf, gaussNorm_pi_single _ _ ρ.2.1]
  simp

theorem extNorm_pow' {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) (x : T.RobbaExt σ) (k : ℕ) :
    T.extNorm σ ρ (x ^ k) = T.extNorm σ ρ x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, extNorm_one]
  | succ k ih => rw [pow_succ, extNorm_mul, ih, pow_succ]

theorem zpow_pow_comm (x : ℝ) (n : ℤ) (q : ℕ) : (x ^ n) ^ q = (x ^ q) ^ n := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast x q, ← zpow_mul, mul_comm]

theorem max_pow_le {a b M : ℝ} {q : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a ^ q ≤ M) (h2 : b ^ q ≤ M) :
    max a b ^ q ≤ M := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

namespace TeichFrob

variable (F : T.TeichFrob) {n : ℕ}

def twistFrob {ρ : Set.Ioo (0 : ℝ) 1} (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ)
    (τ : Set.Ioo (0 : ℝ) 1) (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ)
    (w : Fin n → T.RobbaExt τ) : Fin n → T.RobbaExt (F.powRadius τ) :=
  fun i => T.piInvE (F.powRadius τ) ^ N * ∑ j, T.res hτ (A i j) * F.extFrob τ (w j)

variable {F}
variable {ρ : Set.Ioo (0 : ℝ) 1} (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ)

theorem twistFrob_add {τ : Set.Ioo (0 : ℝ) 1} (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ)
    (w w' : Fin n → T.RobbaExt τ) :
    F.twistFrob A N τ hτ (w + w') = F.twistFrob A N τ hτ w + F.twistFrob A N τ hτ w' := by
  funext i
  simp only [twistFrob, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem twistFrob_neg {τ : Set.Ioo (0 : ℝ) 1} (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ)
    (w : Fin n → T.RobbaExt τ) : F.twistFrob A N τ hτ (-w) = -F.twistFrob A N τ hτ w := by
  funext i
  simp only [twistFrob, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

theorem twistFrob_sub {τ : Set.Ioo (0 : ℝ) 1} (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ)
    (w w' : Fin n → T.RobbaExt τ) :
    F.twistFrob A N τ hτ (w - w') = F.twistFrob A N τ hτ w - F.twistFrob A N τ hτ w' := by
  rw [sub_eq_add_neg, twistFrob_add, twistFrob_neg, ← sub_eq_add_neg]

theorem twistFrob_res {τ τ' : Set.Ioo (0 : ℝ) 1} (h : (τ' : ℝ) ≤ τ)
    (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ)
    (hτ' : ((F.powRadius τ' : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ) (w : Fin n → T.RobbaExt τ) :
    F.twistFrob A N τ' hτ' (fun j => T.res h (w j)) =
      fun i => T.res (F.powRadius_le h) (F.twistFrob A N τ hτ w i) := by
  funext i
  simp only [twistFrob, map_mul, map_pow, map_sum, res_piInvE, res_res, ← F.res_extFrob]

theorem extNorm_twistFrob_le {τ : Set.Ioo (0 : ℝ) 1}
    (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ) (w : Fin n → T.RobbaExt τ)
    (r : Set.Ioc (0 : ℝ) τ) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hA : ∀ i j, T.extNorm ρ ⟨_, (F.powRad r).2.1, (F.powRad r).2.2.trans hτ⟩ (A i j) ≤ K)
    (hw : ∀ j, T.extNorm τ r (w j) ^ p ^ F.a ≤ M) (i : Fin n) :
    T.extNorm (F.powRadius τ) (F.powRad r) (F.twistFrob A N τ hτ w i) ≤
      (((r : ℝ) ^ p ^ F.a) ^ N)⁻¹ * (K * M) := by
  rw [twistFrob, extNorm_mul, extNorm_pow', extNorm_piInvE, coe_powRad, inv_pow]
  refine mul_le_mul_of_nonneg_left (extNorm_sum_le _ _ _ (mul_nonneg hK hM) fun j _ => ?_)
    (inv_nonneg.2 (pow_nonneg (pow_nonneg r.2.1.le _) _))
  rw [extNorm_mul, extNorm_res, extNorm_extFrob]
  exact mul_le_mul (hA i j) (hw j) (pow_nonneg (T.extNorm_nonneg _ _) _) hK

def untwist (A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ) (w : Fin n → T.RobbaExt ρ) :
    Fin n → T.RobbaExt (F.rootRadius ρ) :=
  fun i => F.extFrobSymm ρ (T.piE ρ ^ N * (A'.mulVec w) i)

theorem le_rootRadius (τ : Set.Ioo (0 : ℝ) 1) : (τ : ℝ) ≤ F.rootRadius τ :=
  Real.self_le_rpow_of_le_one τ.2.1.le τ.2.2.le
    (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 F.q_pos.ne'))

theorem twistFrob_res_untwist (A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1)
    (w : Fin n → T.RobbaExt ρ) :
    F.twistFrob A N ρ (F.powRadius_le_self ρ)
        (fun i => T.res (F.le_rootRadius ρ) (F.untwist A' N w i)) =
      fun i => T.res (F.powRadius_le_self ρ) (w i) := by
  funext i
  simp only [twistFrob, untwist]
  have h1 : ∀ j, F.extFrob ρ (T.res (F.le_rootRadius ρ) (F.extFrobSymm ρ
      (T.piE ρ ^ N * (A'.mulVec w) j))) =
      T.res (F.powRadius_le_self ρ) (T.piE ρ ^ N * (A'.mulVec w) j) := fun j =>
    F.extFrob_res_extFrobSymm _ _ _
  simp only [h1, ← map_mul, ← map_sum]
  have h2 : ∑ j, A i j * (T.piE ρ ^ N * (A'.mulVec w) j) = T.piE ρ ^ N * w i := by
    have : ∑ j, A i j * (T.piE ρ ^ N * (A'.mulVec w) j) =
        T.piE ρ ^ N * (A.mulVec (A'.mulVec w)) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  rw [h2, map_mul, map_pow, res_piE, ← mul_assoc, ← mul_pow, mul_comm (T.piInvE _),
    piE_mul_piInvE, one_pow, one_mul]

theorem extNorm_untwist_pow_le (A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (w : Fin n → T.RobbaExt ρ)
    (s : Set.Ioc (0 : ℝ) (F.rootRadius ρ)) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hA : ∀ i j, T.extNorm ρ (F.powRadRoot s) (A' i j) ≤ K)
    (hw : ∀ j, T.extNorm ρ (F.powRadRoot s) (w j) ≤ M) (i : Fin n) :
    T.extNorm (F.rootRadius ρ) s (F.untwist A' N w i) ^ p ^ F.a ≤
      ((s : ℝ) ^ p ^ F.a) ^ N * (K * M) := by
  rw [untwist, extNorm_extFrobSymm, extNorm_mul, extNorm_pow', extNorm_piE, coe_powRadRoot]
  simp only [Matrix.mulVec, dotProduct]
  refine mul_le_mul_of_nonneg_left (extNorm_sum_le _ _ _ (mul_nonneg hK hM) fun j _ => ?_)
    (pow_nonneg (pow_nonneg s.2.1.le _) _)
  rw [extNorm_mul]
  exact mul_le_mul (hA i j) (hw j) (T.extNorm_nonneg _ _) hK

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem mul_pow_mul_pow_pred_le {c S θ : ℝ} {q : ℕ} (hq : 1 ≤ q) (hθ : 0 ≤ θ) (hθc : θ ≤ c)
    (hS : 0 ≤ S) : c * S ^ q * θ ^ (q - 1) ≤ (c * S) ^ q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc c * S ^ (k + 1) * θ ^ k ≤ c * S ^ (k + 1) * c ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ hθc k)
          (mul_nonneg (hθ.trans hθc) (pow_nonneg hS _))
    _ = (c * S) ^ (k + 1) := by ring

namespace TeichFrob

variable (F : T.TeichFrob) {n : ℕ}

def radPow (ρ : Set.Ioo (0 : ℝ) 1) : Set.Ioc (0 : ℝ) ρ :=
  ⟨(F.powRadius ρ : ℝ), (F.powRadius ρ).2.1, F.powRadius_le_self ρ⟩

def radPow2 (ρ : Set.Ioo (0 : ℝ) 1) : Set.Ioc (0 : ℝ) ρ :=
  ⟨(F.powRadius (F.powRadius ρ) : ℝ), (F.powRadius (F.powRadius ρ)).2.1,
    (F.powRadius_le_self _).trans (F.powRadius_le_self ρ)⟩

variable {F}

theorem exists_solve_approx (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1) (N : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hAσ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A i j) ≤ C)
    (hA'σ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A' i j) ≤ C)
    (hA'σ2 : ∀ i j, T.extNorm ρ (F.radPow2 ρ) (A' i j) ≤ C)
    (hN : 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1)
    (y : Fin n → T.B) (hy : ∀ i, T.ConvAll (y i)) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : ∀ i, gaussNorm (T.coeffB (y i)) (F.powRadius ρ) ≤ Y) :
    ∃ z : Fin n → T.RobbaExt ρ,
      (∀ i, T.extNorm (F.powRadius ρ) (topRad _) (F.twistFrob A N ρ (F.powRadius_le_self ρ) z i -
        T.res (F.powRadius_le_self ρ) (z i) - T.ofAll (y i) (hy i) (F.powRadius ρ)) ≤ Y / 2) ∧
      (∀ i, T.extNorm ρ (F.radPow ρ) (z i) ≤ Y) ∧
      (∀ i, T.extNorm ρ (topRad ρ) (z i) ^ p ^ F.a ≤ C * Y) := by
  have hq2 : 2 ≤ p ^ F.a := F.two_le_q ha
  have hq0 : p ^ F.a ≠ 0 := by omega
  have hρ0 : (0 : ℝ) < ρ := ρ.2.1
  have hρ1 : (ρ : ℝ) < 1 := ρ.2.2
  have hσ0 : (0 : ℝ) < F.powRadius ρ := (F.powRadius ρ).2.1
  have hσ1 : (F.powRadius ρ : ℝ) < 1 := (F.powRadius ρ).2.2
  have hσρ : (F.powRadius ρ : ℝ) ≤ ρ := F.powRadius_le_self ρ
  have hρr : (ρ : ℝ) ≤ F.rootRadius ρ := F.le_rootRadius ρ
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hκ0 : 0 < (F.powRadius ρ : ℝ) ^ N := pow_pos hσ0 N
  have hκ1 : (F.powRadius ρ : ℝ) ^ N ≤ 1 := pow_le_one₀ hσ0.le hσ1.le
  have hlam0 : 0 ≤ (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) := pow_nonneg hσ0.le _

  set θ : ℝ := ((F.powRadius ρ : ℝ) ^ N / (2 * C)) ^ (((p ^ F.a - 1 : ℕ) : ℝ)⁻¹) with hθdef
  have h2C : 0 < 2 * C := mul_pos two_pos hC0
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos (div_pos hκ0 h2C) _
  have hθq : θ ^ (p ^ F.a - 1) = (F.powRadius ρ : ℝ) ^ N / (2 * C) :=
    Real.rpow_inv_natCast_pow (div_pos hκ0 h2C).le (by omega)
  have hθC : θ ^ (p ^ F.a - 1) ≤ C := by
    rw [hθq, div_le_iff₀ h2C]; nlinarith

  set ys : Fin n → T.B := fun i => T.smallPart θ (y i) with hysdef
  set yb : Fin n → T.B := fun i => T.bigPart θ (y i) with hybdef
  have hys : ∀ i, T.ConvAll (ys i) := fun i r h0 h1 =>
    (convergesAt_of_norm_le h0 (T.norm_coeffB_smallPart_le hθ0 _) (hy i r h0 h1)).1
  have hyb : ∀ i, T.ConvAll (yb i) := fun i r h0 h1 =>
    (convergesAt_of_norm_le h0 (T.norm_coeffB_bigPart_le θ _) (hy i r h0 h1)).1
  have hysσ : ∀ i, gaussNorm (T.coeffB (ys i)) (F.powRadius ρ) ≤ Y := fun i =>
    (convergesAt_of_norm_le hσ0 (T.norm_coeffB_smallPart_le hθ0 _) (hy i _ hσ0 hσ1)).2.trans (hY i)
  have hybσ : ∀ i, gaussNorm (T.coeffB (yb i)) (F.powRadius ρ) ≤ Y := fun i =>
    (convergesAt_of_norm_le hσ0 (T.norm_coeffB_bigPart_le θ _) (hy i _ hσ0 hσ1)).2.trans (hY i)

  have hS1 : ∀ i, T.extNorm ρ (topRad ρ) (T.ofAll (ys i) (hys i) ρ) ^ p ^ F.a ≤
      θ ^ (p ^ F.a - 1) * Y := fun i => by
    rw [extNorm_ofAll]
    refine (T.gaussNorm_pow_le hθ0.le (fun k => (T.norm_coeffB_smallPart_lt hθ0 _ k).le)
      (by omega) hρ0 hρ1).trans (mul_le_mul_of_nonneg_left (hysσ i) (by positivity))

  have hB1 : ∀ i, gaussNorm (T.coeffB (yb i)) ((F.powRadius (F.powRadius ρ) : ℝ)) ≤
      Y ^ p ^ F.a / θ ^ (p ^ F.a - 1) := fun i => gaussNorm_le fun k => by
    rcases T.coeffB_bigPart_eq_zero_or θ (y i) k with h | h
    · rw [h, norm_zero, zero_mul]; exact div_nonneg (pow_nonneg hY0 _) (pow_nonneg hθ0.le _)
    · have hw : ‖T.coeffB (yb i) k‖ * (F.powRadius ρ : ℝ) ^ k ≤ Y :=
        (mul_le_mul_of_nonneg_right (T.norm_coeffB_bigPart_le θ _ k) (zpow_pos hσ0 k).le).trans
          (((hy i _ hσ0 hσ1).le_gaussNorm k).trans (hY i))
      rw [le_div_iff₀ (pow_pos hθ0 _)]
      show ‖T.coeffB (yb i) k‖ * ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ k * θ ^ (p ^ F.a - 1) ≤ _
      rw [← zpow_pow_comm]
      exact (mul_pow_mul_pow_pred_le (by omega) hθ0.le h (zpow_pos hσ0 k).le).trans
        (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (zpow_pos hσ0 k).le) hw _)

  set w : Fin n → T.RobbaExt ρ := fun j => T.ofAll (yb j) (hyb j) ρ with hwdef
  set z : Fin n → T.RobbaExt ρ := fun i => -T.ofAll (ys i) (hys i) ρ +
    T.res hρr (F.untwist A' N w i) with hzdef

  let sσ : Set.Ioc (0 : ℝ) (F.rootRadius ρ) := ⟨F.powRadius ρ, hσ0, hσρ.trans hρr⟩
  let sρ : Set.Ioc (0 : ℝ) (F.rootRadius ρ) := ⟨ρ, hρ0, hρr⟩
  have hBσ : ∀ i, T.extNorm (F.rootRadius ρ) sσ (F.untwist A' N w i) ≤ Y / 2 := fun i => by
    have h1 := extNorm_untwist_pow_le N A' w sσ hC0.le
      (div_nonneg (pow_nonneg hY0 _) (pow_nonneg hθ0.le _)) (fun i j => hA'σ2 i j)
      (fun j => by rw [extNorm_ofAll]; exact hB1 j) i
    have hlam : ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ N =
        (F.powRadius ρ : ℝ) ^ N * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) := by
      rw [← pow_mul, ← pow_add]; congr 1
      rw [Nat.mul_sub_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right N (by omega)), mul_comm]
    have h2 : ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ N * (C * (Y ^ p ^ F.a / θ ^ (p ^ F.a - 1))) ≤
        (Y / 2) ^ p ^ F.a := by
      rw [hlam, hθq, div_pow]
      have h8 : 2 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1 := by
        have : 0 ≤ 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) := by positivity
        nlinarith
      rw [le_div_iff₀ (by positivity)]
      have e : (F.powRadius ρ : ℝ) ^ N * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) *
          (C * (Y ^ p ^ F.a / ((F.powRadius ρ : ℝ) ^ N / (2 * C)))) * 2 ^ p ^ F.a =
          (2 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1))) * Y ^ p ^ F.a := by
        field_simp
      rw [e]
      exact (mul_le_mul_of_nonneg_right h8 (pow_nonneg hY0 _)).trans (one_mul _).le
    exact (pow_le_pow_iff_left₀ (T.extNorm_nonneg _ _) (by linarith) hq0).1 (h1.trans h2)
  have hBρ : ∀ i, T.extNorm (F.rootRadius ρ) sρ (F.untwist A' N w i) ^ p ^ F.a ≤ C * Y := fun i => by
    have h1 := extNorm_untwist_pow_le N A' w sρ hC0.le hY0 (fun i j => hA'σ i j)
      (fun j => by rw [extNorm_ofAll]; exact hybσ j) i
    refine h1.trans ?_
    calc ((ρ : ℝ) ^ p ^ F.a) ^ N * (C * Y) ≤ 1 * (C * Y) :=
          mul_le_mul_of_nonneg_right hκ1 (mul_nonneg hC0.le hY0)
      _ = C * Y := one_mul _
  refine ⟨z, fun i => ?_, fun i => ?_, fun i => ?_⟩
  ·
    have hz : z = -(fun j => T.ofAll (ys j) (hys j) ρ) +
        (fun j => T.res hρr (F.untwist A' N w j)) := by
      funext j; simp only [hzdef, Pi.add_apply, Pi.neg_apply]
    have e3 : F.twistFrob A N ρ (F.powRadius_le_self ρ) z i =
        -F.twistFrob A N ρ (F.powRadius_le_self ρ) (fun j => T.ofAll (ys j) (hys j) ρ) i +
          T.ofAll (yb i) (hyb i) (F.powRadius ρ) := by
      rw [hz, twistFrob_add, twistFrob_neg, twistFrob_res_untwist A N A' hAA]
      simp only [Pi.add_apply, Pi.neg_apply, hwdef, res_ofAll]
    have e1 : T.res (F.powRadius_le_self ρ) (z i) = -T.ofAll (ys i) (hys i) (F.powRadius ρ) +
        T.res (hσρ.trans hρr) (F.untwist A' N w i) := by
      simp only [hzdef, map_add, map_neg, res_ofAll, res_res]
    have e2 : T.ofAll (y i) (hy i) (F.powRadius ρ) = T.ofAll (ys i) (hys i) (F.powRadius ρ) +
        T.ofAll (yb i) (hyb i) (F.powRadius ρ) := by
      rw [← ofAll_add]; exact ofAll_congr _ _ (T.smallPart_add_bigPart θ (y i)).symm _
    rw [e3, e1, e2]
    have e : -F.twistFrob A N ρ (F.powRadius_le_self ρ) (fun j => T.ofAll (ys j) (hys j) ρ) i +
        T.ofAll (yb i) (hyb i) (F.powRadius ρ) - (-T.ofAll (ys i) (hys i) (F.powRadius ρ) +
          T.res (hσρ.trans hρr) (F.untwist A' N w i)) -
        (T.ofAll (ys i) (hys i) (F.powRadius ρ) + T.ofAll (yb i) (hyb i) (F.powRadius ρ)) =
        -F.twistFrob A N ρ (F.powRadius_le_self ρ) (fun j => T.ofAll (ys j) (hys j) ρ) i +
          -T.res (hσρ.trans hρr) (F.untwist A' N w i) := by ring
    rw [e]
    refine (T.extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · rw [extNorm_neg]
      have h1 := extNorm_twistFrob_le A N (F.powRadius_le_self ρ) (fun j => T.ofAll (ys j) (hys j) ρ)
        (topRad ρ) hC0.le (by positivity) (fun i j => hAσ i j) hS1 i
      refine h1.trans (le_of_eq ?_)
      show (((ρ : ℝ) ^ p ^ F.a) ^ N)⁻¹ * (C * (θ ^ (p ^ F.a - 1) * Y)) = Y / 2
      rw [hθq]
      field_simp
      rfl
    · rw [extNorm_neg, extNorm_res]; exact hBσ i
  ·
    simp only [hzdef]
    refine (T.extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · rw [extNorm_neg, extNorm_ofAll]; exact hysσ i
    · rw [extNorm_res]; exact (hBσ i).trans (by linarith)
  ·
    simp only [hzdef]
    refine (pow_le_pow_left₀ (T.extNorm_nonneg _ _) (T.extNorm_add_le _ _ _) _).trans
      (max_pow_le (T.extNorm_nonneg _ _) (T.extNorm_nonneg _ _) ?_ ?_)
    · rw [extNorm_neg]
      exact (hS1 i).trans (mul_le_mul_of_nonneg_right hθC hY0)
    · rw [extNorm_res]; exact hBρ i

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob} {n : ℕ}

theorem exists_solve (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1) (N : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hAσ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A i j) ≤ C)
    (hA'σ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A' i j) ≤ C)
    (hA'σ2 : ∀ i j, T.extNorm ρ (F.radPow2 ρ) (A' i j) ≤ C)
    (hN : 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1)
    (e : Fin n → T.RobbaExt (F.powRadius ρ)) {Y : ℝ} (hY : 0 < Y)
    (he : ∀ i, T.extNorm (F.powRadius ρ) (topRad _) (e i) ≤ Y) :
    ∃ z : Fin n → T.RobbaExt ρ,
      (∀ i, T.extNorm (F.powRadius ρ) (topRad _) (e i - (F.twistFrob A N ρ (F.powRadius_le_self ρ)
        z i - T.res (F.powRadius_le_self ρ) (z i))) ≤ Y / 2) ∧
      (∀ i, T.extNorm ρ (F.radPow ρ) (z i) ≤ Y) ∧
      (∀ i, T.extNorm ρ (topRad ρ) (z i) ^ p ^ F.a ≤ C * Y) := by
  choose d hd hde using fun i => exists_approx_convAll (e i) (topRad (F.powRadius ρ)) (half_pos hY)
  have hdY : ∀ i, gaussNorm (T.coeffB (d i)) (F.powRadius ρ) ≤ Y := fun i => by
    have h := extNorm_ofAll (hd i) (topRad (F.powRadius ρ))
    change T.extNorm _ _ _ = gaussNorm (T.coeffB (d i)) (F.powRadius ρ) at h
    rw [← h, show T.ofAll (d i) (hd i) (F.powRadius ρ) = e i + -(e i - T.ofAll (d i) (hd i) _) by ring]
    exact (T.extNorm_add_le _ _ _).trans (max_le (he i) (by
      rw [extNorm_neg]; exact (hde i _ le_rfl).trans (by linarith)))
  obtain ⟨z, h1, h2, h3⟩ := exists_solve_approx ha A A' hAA N hC hAσ hA'σ hA'σ2 hN d hd hY.le hdY
  refine ⟨z, fun i => ?_, h2, h3⟩
  have e1 : e i - (F.twistFrob A N ρ (F.powRadius_le_self ρ) z i - T.res (F.powRadius_le_self ρ) (z i)) =
      (e i - T.ofAll (d i) (hd i) _) + -(F.twistFrob A N ρ (F.powRadius_le_self ρ) z i -
        T.res (F.powRadius_le_self ρ) (z i) - T.ofAll (d i) (hd i) _) := by ring
  rw [e1]
  refine (T.extNorm_add_le _ _ _).trans (max_le (hde i _ le_rfl) ?_)
  rw [extNorm_neg]; exact h1 i

theorem exists_solve_seq (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1) (N : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hAσ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A i j) ≤ C)
    (hA'σ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A' i j) ≤ C)
    (hA'σ2 : ∀ i j, T.extNorm ρ (F.radPow2 ρ) (A' i j) ≤ C)
    (hN : 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1)
    (e0 : Fin n → T.RobbaExt (F.powRadius ρ)) {E : ℝ} (hE : 0 < E)
    (he0 : ∀ i, T.extNorm (F.powRadius ρ) (topRad _) (e0 i) ≤ E) :
    ∃ (e : ℕ → Fin n → T.RobbaExt (F.powRadius ρ)) (z : ℕ → Fin n → T.RobbaExt ρ), e 0 = e0 ∧
      (∀ j, e (j + 1) = e j - (F.twistFrob A N ρ (F.powRadius_le_self ρ) (z j) -
        fun i => T.res (F.powRadius_le_self ρ) (z j i))) ∧
      (∀ j i, T.extNorm (F.powRadius ρ) (topRad _) (e j i) ≤ E / 2 ^ j) ∧
      (∀ j i, T.extNorm ρ (F.radPow ρ) (z j i) ≤ E / 2 ^ j) ∧
      (∀ j i, T.extNorm ρ (topRad ρ) (z j i) ^ p ^ F.a ≤ C * (E / 2 ^ j)) := by
  have step : ∀ (e : Fin n → T.RobbaExt (F.powRadius ρ)) (Y : ℝ), ∃ z : Fin n → T.RobbaExt ρ,
      0 < Y → (∀ i, T.extNorm (F.powRadius ρ) (topRad _) (e i) ≤ Y) →
      (∀ i, T.extNorm (F.powRadius ρ) (topRad _) (e i - (F.twistFrob A N ρ (F.powRadius_le_self ρ)
        z i - T.res (F.powRadius_le_self ρ) (z i))) ≤ Y / 2) ∧
      (∀ i, T.extNorm ρ (F.radPow ρ) (z i) ≤ Y) ∧
      (∀ i, T.extNorm ρ (topRad ρ) (z i) ^ p ^ F.a ≤ C * Y) := by
    intro e Y
    by_cases h : 0 < Y ∧ ∀ i, T.extNorm (F.powRadius ρ) (topRad _) (e i) ≤ Y
    · obtain ⟨z, hz⟩ := exists_solve ha A A' hAA N hC hAσ hA'σ hA'σ2 hN e h.1 h.2
      exact ⟨z, fun _ _ => hz⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using step
  let D : (Fin n → T.RobbaExt ρ) → Fin n → T.RobbaExt (F.powRadius ρ) := fun z =>
    F.twistFrob A N ρ (F.powRadius_le_self ρ) z - fun i => T.res (F.powRadius_le_self ρ) (z i)
  let e : ℕ → Fin n → T.RobbaExt (F.powRadius ρ) := fun j =>
    Nat.rec e0 (fun j ej => ej - D (g ej (E / 2 ^ j))) j
  have he : ∀ j i, T.extNorm (F.powRadius ρ) (topRad _) (e j i) ≤ E / 2 ^ j := by
    intro j
    induction j with
    | zero =>
      intro i
      show T.extNorm _ _ (e0 i) ≤ E / 2 ^ 0
      simpa using he0 i
    | succ j ih =>
      intro i
      have := (hg (e j) (E / 2 ^ j) (by positivity) ih).1 i
      rw [pow_succ, ← div_div]
      exact this
  refine ⟨e, fun j => g (e j) (E / 2 ^ j), rfl, fun j => rfl, he, fun j i => ?_, fun j i => ?_⟩
  · exact (hg (e j) (E / 2 ^ j) (by positivity) (he j)).2.1 i
  · exact (hg (e j) (E / 2 ^ j) (by positivity) (he j)).2.2 i

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
