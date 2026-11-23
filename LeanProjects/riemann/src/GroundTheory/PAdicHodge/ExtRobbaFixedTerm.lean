import Mathlib
import GroundTheory.PAdicHodge.DMTeichBasic
import GroundTheory.PAdicHodge.DMTeichPow
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

abbrev πB : T.B := algebraMap Γ T.B T.π

theorem πB_ne_zero : T.πB ≠ 0 := by
  have := T.nontrivial_B
  exact (IsLocalization.Away.algebraMap_isUnit T.π).ne_zero

def DigLe (x : Γ) (Θ : ℝ) : Prop := ∀ n, ‖T.coeff x n‖ ≤ Θ

def IsUnitTerm (P : T.B) (i : ℤ) : Prop :=
  ∃ U ∈ T.int, ‖T.red U‖ = 1 ∧ P = T.πB ^ i * algebraMap Γ T.B U

variable {T}

theorem digLe_iff_prefixLe {x : Γ} {Θ : ℝ} : T.DigLe x Θ ↔ ∀ n, T.PrefixLe x n Θ :=
  ⟨fun h _ m _ => h m, fun h n => h n n le_rfl⟩

theorem DigLe.mono {x : Γ} {Θ Θ' : ℝ} (h : T.DigLe x Θ) (hΘ : Θ ≤ Θ') : T.DigLe x Θ' :=
  fun n => (h n).trans hΘ

theorem DigLe.add {x y : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hy : T.DigLe y Θ) : T.DigLe (x + y) Θ :=
  digLe_iff_prefixLe.2 fun n =>
    T.prefixLe_add (digLe_iff_prefixLe.1 hx n) (digLe_iff_prefixLe.1 hy n)

theorem digLe_teich {a : L} {Θ : ℝ} (h : ‖a‖ ≤ Θ) : T.DigLe (T.teich a) Θ := fun n => by
  rw [T.coeff_teich]
  split_ifs
  · exact h
  · simpa using (norm_nonneg a).trans h

theorem digLe_π_mul_iff {x : Γ} {Θ : ℝ} (hΘ : 0 ≤ Θ) : T.DigLe (T.π * x) Θ ↔ T.DigLe x Θ := by
  constructor
  · intro h n; rw [← T.coeff_π_mul_succ]; exact h (n + 1)
  · intro h n
    cases n with
    | zero => rw [T.coeff_zero, map_mul, T.red_π, zero_mul, norm_zero]; exact hΘ
    | succ n => rw [T.coeff_π_mul_succ]; exact h n

theorem digLe_one_of_mem_int {x : Γ} (hx : x ∈ T.int) : T.DigLe x 1 := T.mem_int_iff.1 hx

theorem DigLe.convergesAt {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ConvergesAt (T.zcoeff x) r :=
  T.convergesAt_of_forall_weight_le (ρ := 1) (Y := Θ) hr0 hr1 fun n => by
    rw [one_pow, mul_one]; exact hx n

theorem DigLe.gaussNorm_le {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) : gaussNorm (T.zcoeff x) r ≤ Θ :=
  ciSup_le fun j => T.zcoeff_weight_le hΘ (fun n =>
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr0.le hr1.le)).trans (hx n)) j

theorem DigLe.convAll {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) : T.ConvAll (algebraMap Γ T.B x) :=
  fun _ hr0 hr1 => by rw [T.coeffB_algebraMap]; exact hx.convergesAt hr0 hr1

theorem convAll_πB_zpow (i : ℤ) : T.ConvAll (T.πB ^ i) := by
  have hinv : (T.πB)⁻¹ = IsLocalization.Away.invSelf T.π :=
    inv_eq_of_mul_eq_one_right (IsLocalization.Away.mul_invSelf T.π)
  have hc : T.ConvAll (IsLocalization.Away.invSelf T.π) := fun ρ _ _ => by
    rw [T.coeffB_invSelf]; exact convergesAt_pi_single _ _ _
  have hpow : ∀ n : ℕ, T.ConvAll ((IsLocalization.Away.invSelf T.π) ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero]
      simpa using (convAll_π_pow (T := T) 0)
    | succ n ih => rw [pow_succ]; exact ih.mul hc
  rcases i with n | n
  · simpa [zpow_natCast] using (convAll_π_pow (T := T) n)
  · rw [zpow_negSucc, ← inv_pow, hinv]; exact hpow _

theorem convAll_algebraMap_of_mem_int {U : Γ} (hU : U ∈ T.int) :
    T.ConvAll (algebraMap Γ T.B U) := (digLe_one_of_mem_int hU).convAll

theorem coeffB_πB_zpow_mul (i : ℤ) (x : Γ) :
    T.coeffB (T.πB ^ i * algebraMap Γ T.B x) = fun k => T.zcoeff x (k - i) := by
  set N := (-i).toNat
  set M := i.toNat
  have hNM : i + (N : ℤ) = M := by have := Int.toNat_sub_toNat_neg i; omega
  have h : T.πB ^ i * algebraMap Γ T.B x * algebraMap Γ T.B T.π ^ N =
      algebraMap Γ T.B (T.π ^ M * x) := by
    rw [map_mul, map_pow, mul_right_comm, ← zpow_natCast, ← zpow_add₀ T.πB_ne_zero, hNM,
      zpow_natCast]
  rw [T.coeffB_eq h]
  funext k
  have := T.zcoeff_π_pow_mul M x (k - i)
  rw [show k - i + (M : ℤ) = k + (N : ℤ) by omega] at this
  exact this

theorem isUnitTerm_one : T.IsUnitTerm 1 0 :=
  ⟨1, T.int.one_mem, by simp, by simp⟩

theorem isUnitTerm_πB_zpow (i : ℤ) : T.IsUnitTerm (T.πB ^ i) i :=
  ⟨1, T.int.one_mem, by simp, by simp⟩

theorem isUnitTerm_algebraMap {U : Γ} (hU : U ∈ T.int) (h1 : ‖T.red U‖ = 1) :
    T.IsUnitTerm (algebraMap Γ T.B U) 0 :=
  ⟨U, hU, h1, by simp⟩

theorem IsUnitTerm.congr_idx {P : T.B} {i j : ℤ} (h : T.IsUnitTerm P i) (hij : i = j) :
    T.IsUnitTerm P j := hij ▸ h

theorem IsUnitTerm.mul {P P' : T.B} {i i' : ℤ} (h : T.IsUnitTerm P i) (h' : T.IsUnitTerm P' i') :
    T.IsUnitTerm (P * P') (i + i') := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  obtain ⟨U', hU', hU1', rfl⟩ := h'
  refine ⟨U * U', T.int.mul_mem hU hU', by rw [map_mul, norm_mul, hU1, hU1', one_mul], ?_⟩
  rw [zpow_add₀ T.πB_ne_zero, map_mul]; ring

theorem IsUnitTerm.inv {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.IsUnitTerm P⁻¹ (-i) := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  obtain ⟨V, hV, hUV⟩ := T.exists_inv_mem_int hU hU1
  have hV1 : ‖T.red V‖ = 1 := by
    have := congrArg (fun y => ‖T.red y‖) hUV
    simpa [map_mul, norm_mul, hU1] using this
  refine ⟨V, hV, hV1, ?_⟩
  have hUVB : algebraMap Γ T.B U * algebraMap Γ T.B V = 1 := by rw [← map_mul, hUV, map_one]
  rw [mul_inv, zpow_neg, inv_eq_of_mul_eq_one_right hUVB]

theorem IsUnitTerm.ne_zero {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : P ≠ 0 := by
  intro h0
  obtain ⟨U, hU, hU1, hP⟩ := h.inv
  rw [h0, inv_zero] at hP
  have hU0 : algebraMap Γ T.B U = 0 := by
    rcases mul_eq_zero.1 hP.symm with h1 | h1
    · exact absurd h1 (zpow_ne_zero _ T.πB_ne_zero)
    · exact h1
  have : U = 0 := T.algebraMap_injective (by rw [hU0, map_zero])
  rw [this, map_zero, norm_zero] at hU1
  exact zero_ne_one hU1

theorem IsUnitTerm.zpow {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) (k : ℤ) :
    T.IsUnitTerm (P ^ k) (k * i) := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero]; exact isUnitTerm_one.congr_idx (by ring)
  | succ k ih => rw [zpow_add_one₀ h.ne_zero]; exact (ih.mul h).congr_idx (by ring)
  | pred k ih =>
    rw [zpow_sub_one₀ h.ne_zero]; exact (ih.mul h.inv).congr_idx (by ring)

theorem IsUnitTerm.convAll {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.ConvAll P := by
  obtain ⟨U, hU, -, rfl⟩ := h
  exact (convAll_πB_zpow i).mul (convAll_algebraMap_of_mem_int hU)

theorem gaussNorm_single_zero (c : L) (r : ℝ) :
    gaussNorm (Pi.single 0 c) r = ‖c‖ := by
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · calc ‖c‖ = ‖(Pi.single (0 : ℤ) c : ℤ → L) 0‖ * r ^ (0 : ℤ) := by simp
      _ ≤ gaussNorm (Pi.single 0 c) r :=
        le_ciSup (f := fun n : ℤ => ‖(Pi.single (0 : ℤ) c : ℤ → L) n‖ * r ^ n)
          (convergesAt_pi_single (0 : ℤ) c r).bddAbove 0

theorem IsUnitTerm.gaussNorm_mul_teich {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) (a : L) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    gaussNorm (T.coeffB (P * algebraMap Γ T.B (T.teich a))) r = r ^ i * ‖a‖ := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  rw [mul_assoc, ← map_mul, coeffB_πB_zpow_mul]
  have e : (fun k => T.zcoeff (U * T.teich a) (k - i)) =
      fun k => T.zcoeff (U * T.teich a) (k + -i) := by funext k; rw [sub_eq_add_neg]
  rw [e, gaussNorm_shift hr0, neg_neg,
    T.gaussNorm_zcoeff_mul hr0 hr1 (T.convergesAt_of_mem_int hU hr0 hr1)
      ((digLe_teich (T := T) (le_refl ‖a‖)).convergesAt hr0 hr1),
    T.gaussNorm_eq_one_of_mem_int hU hU1 hr0 hr1, T.zcoeff_teich, gaussNorm_single_zero a r]
  ring

namespace TeichFrob

variable (F : T.TeichFrob)

def frobPow (k : ℤ) (a : L) : L := ((iterateFrobeniusEquiv L p F.a : RingAut L) ^ k) a

theorem IsUnitTerm.toB {P : T.B} {i : ℤ} (h : T.IsUnitTerm P i) : T.IsUnitTerm (F.toB P) i := by
  obtain ⟨U, hU, hU1, rfl⟩ := h
  have hπt : T.IsUnitTerm (F.toB T.πB) 1 := by
    have h1 := (isUnitTerm_πB_zpow (T := T) 1).mul (isUnitTerm_algebraMap F.u_mem_int F.norm_red_u)
    rw [zpow_one, add_zero] at h1
    rw [F.toB_algebraMap, F.φ_π, map_mul]
    exact h1
  have hUt : T.IsUnitTerm (F.toB (algebraMap Γ T.B U)) 0 := by
    rw [F.toB_algebraMap]
    refine isUnitTerm_algebraMap (F.map_int U hU) ?_
    rw [F.red_φ, norm_pow, hU1, one_pow]
  rw [map_mul, map_zpow₀]
  exact ((hπt.zpow i).mul hUt).congr_idx (by ring)

def twist (t : T.B) (ht : t ≠ 0) : AddAut T.B where
  toFun b := t * F.toB b
  invFun b := F.toB.symm (t⁻¹ * b)
  left_inv b := by simp [ht]
  right_inv b := by simp [ht]
  map_add' b c := by simp [mul_add]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
