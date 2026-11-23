import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown
import Lemmata.PeriodicFunctions.PeriodicApplyMulAdd

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Perm

variable {K : Type} [Field K]

theorem perm_range (M : ℕ) (f : ℕ → ℕ) (hf : ∀ i < M, f i < M)
    (hinj : ∀ i < M, ∀ j < M, f i = f j → i = j) (g : ℕ → K) :
    ∑ i ∈ Finset.range M, g (f i) = ∑ i ∈ Finset.range M, g i := by
  have hI : Set.InjOn f (Finset.range M : Set ℕ) := fun i hi j hj h =>
    hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h
  rw [← Finset.sum_image (g := f) hI]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hf i (Finset.mem_range.1 hi))
  · rw [Finset.card_image_of_injOn hI]

theorem sum_range_mul (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  first | exact Bl.PeriodicFunctions.goal1 .. | (apply Bl.PeriodicFunctions.goal1 <;> assumption) | (intros; apply Bl.PeriodicFunctions.goal1 <;> assumption)

end Perm

variable {E K : Type} [Field E] [NumberField E] [Field K]

def Sg (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) (φ : E → K) : K :=
  ∑ i ∈ Finset.range (qOf P ^ (A + B)), φ ((i : E) / (qOf P : E) ^ A)

def W1 (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) (φ : E → K) : K := ((qOf P : K) ^ B)⁻¹ * Sg P A B φ

def Good1 (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ) (φ : E → K) : Prop :=
  (∀ u, φ u ≠ 0 → IntAt P ((qOf P : E) ^ a * u)) ∧
  (∀ u δ, IntAt P (δ / (qOf P : E) ^ b) → φ (u + δ) = φ u)

variable {P : HeightOneSpectrum (𝓞 E)}

theorem sum_vals (hp : (Ideal.absNorm P.asIdeal).Prime) (A B : ℕ) (φ : E → K) :
    ∑ u ∈ valsQ E (qOf P) A B, φ u = Sg P A B φ := by
  classical
  have hq := pow_ne_zero A (qE_ne P hp)
  unfold valsQ Sg
  rw [Finset.sum_image]
  intro x _ y _ hxy
  have h2 : ((x : ℕ) : E) = y := by
    have := congrArg (· * (qOf P : E) ^ A) hxy
    simpa [div_mul_cancel₀ _ hq] using this
  exact_mod_cast h2

theorem good_function_mono {a b a' : ℕ} (ha : a ≤ a') {φ : E → K} (h : Good1 P a b φ) : Good1 P a' b φ :=
  ⟨fun u hu => ia_up P ha (h.1 u hu), h.2⟩

section Main

variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq

theorem sg_stab {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B) {φ : E → K} (h : Good1 P a b φ) :
    Sg P A B φ = ((qOf P ^ (B - b) : ℕ) : K) * Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos

  have s1 : Sg P A B φ = ∑ i ∈ Finset.range (qOf P ^ (a + B)), φ ((i : E) / (qOf P : E) ^ a) := by
    unfold Sg
    have hI : Set.InjOn (fun i : ℕ => qOf P ^ (A - a) * i) (Finset.range (qOf P ^ (a + B)) : Set ℕ) :=
      fun i _ j _ h => Nat.eq_of_mul_eq_mul_left (pow_pos qp _) h
    have hsub : (Finset.range (qOf P ^ (a + B))).image (fun i : ℕ => qOf P ^ (A - a) * i) ⊆
        Finset.range (qOf P ^ (A + B)) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at hi ⊢
      have : A + B = (A - a) + (a + B) := by omega
      rw [this, pow_add]
      exact Nat.mul_lt_mul_of_pos_left hi (pow_pos qp _)
    rw [← Finset.sum_subset hsub, Finset.sum_image hI]
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      have : (qOf P : E) ^ A = (qOf P : E) ^ (A - a) * (qOf P : E) ^ a := by
        rw [← pow_add, Nat.sub_add_cancel hA]
      rw [this]
      field_simp
    · intro i hi hni
      by_contra hne
      have h1 := h.1 _ hne
      have e : (qOf P : E) ^ a * ((i : E) / (qOf P : E) ^ A) = (i : E) / (qOf P : E) ^ (A - a) := by
        have : (qOf P : E) ^ A = (qOf P : E) ^ (A - a) * (qOf P : E) ^ a := by
          rw [← pow_add, Nat.sub_add_cancel hA]
        rw [this]
        field_simp
      rw [e, hN.1 E P hp hq] at h1
      obtain ⟨i', rfl⟩ := h1
      apply hni
      refine Finset.mem_image.2 ⟨i', Finset.mem_range.2 ?_, rfl⟩
      have hi' := Finset.mem_range.1 hi
      have : A + B = (A - a) + (a + B) := by omega
      rw [this, pow_add] at hi'
      exact Nat.lt_of_mul_lt_mul_left hi'

  rw [s1]
  have e2 : qOf P ^ (a + B) = qOf P ^ (a + b) * qOf P ^ (B - b) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e2, sum_range_mul]
  · rfl
  · intro i
    have e3 : (((i + qOf P ^ (a + b) : ℕ) : E) / (qOf P : E) ^ a) = (i : E) / (qOf P : E) ^ a + (qOf P : E) ^ b := by
      push_cast
      rw [pow_add]
      field_simp
    rw [e3]
    apply h.2
    rw [div_self (pow_ne_zero _ hq0)]
    exact ia_one P

include hK in
theorem weighted_sum_stable {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B) {φ : E → K} (h : Good1 P a b φ) :
    W1 P A B φ = W1 P a b φ := by
  unfold W1
  rw [sg_stab hN hp hq hA hB h]
  push_cast
  have e : (qOf P : K) ^ B = (qOf P : K) ^ (B - b) * (qOf P : K) ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hB]
  rw [e]
  field_simp

theorem sg_transl {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) {β : E} (hβ : IntAt P ((qOf P : E) ^ a * β)) :
    Good1 P a b (fun u => φ (u + β)) ∧ Sg P a b (fun u => φ (u + β)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = (qOf P : E) ^ a * (u + β) - (qOf P : E) ^ a * β := by ring
    rw [e]
    exact ia_sub P h1 hβ
  · show φ (u + δ + β) = φ (u + β)
    rw [add_right_comm]
    exact h.2 _ _ hδ
  · obtain ⟨j, -, hj⟩ := hN.2.1 E P hp hq _ (a + b) hβ
    set M := qOf P ^ (a + b) with hM
    have Mpos : 0 < M := pow_pos qp _
    unfold Sg
    rw [← hM]
    have key : ∀ i : ℕ, φ ((i : E) / (qOf P : E) ^ a + β) = φ ((((i + j) % M : ℕ) : E) / (qOf P : E) ^ a) := by
      intro i
      have hd := congrArg (Nat.cast (R := E)) (Nat.mod_add_div (i + j) M)
      push_cast at hd
      have e : (i : E) / (qOf P : E) ^ a + β = (((i + j) % M : ℕ) : E) / (qOf P : E) ^ a +
          ((((i + j) / M : ℕ) : E) * (qOf P : E) ^ b + (β - (j : E) / (qOf P : E) ^ a)) := by
        have hr : (((i + j) % M : ℕ) : E) = (i : E) + j - (qOf P : E) ^ (a + b) * (((i + j) / M : ℕ) : E) := by
          rw [hM] at hd
          push_cast at hd ⊢
          linear_combination hd
        rw [hr, pow_add]
        field_simp
        ring
      rw [e]
      apply h.2
      have e2 : ((((i + j) / M : ℕ) : E) * (qOf P : E) ^ b + (β - (j : E) / (qOf P : E) ^ a)) / (qOf P : E) ^ b =
          (((i + j) / M : ℕ) : E) + ((qOf P : E) ^ a * β - j) / (qOf P : E) ^ (a + b) := by
        rw [pow_add]
        field_simp
      rw [e2]
      exact ia_add P (ia_nat P _) hj
    simp only [key]
    exact perm_range M (fun i => (i + j) % M) (fun i _ => Nat.mod_lt _ Mpos)
      (fun i hi i' hi' hii => by
        have h3 : i % M = i' % M := Nat.ModEq.add_right_cancel' j hii
        rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h3)
      (fun i => φ ((i : E) / (qOf P : E) ^ a))

theorem sg_unit {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) {w : E} (hw : UnitAt P w) :
    Good1 P a b (fun u => φ (w * u)) ∧ Sg P a b (fun u => φ (w * u)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = w⁻¹ * ((qOf P : E) ^ a * (w * u)) := by
      field_simp [hw.1]
    rw [e]
    exact ia_mul P hw.2.2 h1
  · show φ (w * (u + δ)) = φ (w * u)
    rw [mul_add]
    apply h.2
    rw [mul_div_assoc]
    exact ia_mul P hw.2.1 hδ
  · obtain ⟨w0, hco, hw0⟩ := hN.2.2.2.2 E P hp hq w (a + b) hw.1 hw.2.1 hw.2.2
    set M := qOf P ^ (a + b) with hM
    have Mpos : 0 < M := pow_pos qp _
    unfold Sg
    rw [← hM]
    have key : ∀ i : ℕ, φ (w * ((i : E) / (qOf P : E) ^ a)) = φ ((((w0 * i) % M : ℕ) : E) / (qOf P : E) ^ a) := by
      intro i
      have hd := congrArg (Nat.cast (R := E)) (Nat.mod_add_div (w0 * i) M)
      have e : w * ((i : E) / (qOf P : E) ^ a) = (((w0 * i) % M : ℕ) : E) / (qOf P : E) ^ a +
          ((((w0 * i) / M : ℕ) : E) * (qOf P : E) ^ b + (w - w0) * (i : E) / (qOf P : E) ^ a) := by
        have hr : (((w0 * i) % M : ℕ) : E) = (w0 : E) * i - (qOf P : E) ^ (a + b) * (((w0 * i) / M : ℕ) : E) := by
          rw [hM] at hd
          push_cast at hd ⊢
          linear_combination hd
        rw [hr, pow_add]
        field_simp
        ring
      rw [e]
      apply h.2
      have e2 : ((((w0 * i) / M : ℕ) : E) * (qOf P : E) ^ b + (w - w0) * (i : E) / (qOf P : E) ^ a) / (qOf P : E) ^ b =
          (((w0 * i) / M : ℕ) : E) + (i : E) * ((w - w0) / (qOf P : E) ^ (a + b)) := by
        rw [pow_add]
        field_simp
      rw [e2]
      exact ia_add P (ia_nat P _) (ia_mul P (ia_nat P _) hw0)
    simp only [key]
    have hcoM : Nat.gcd M w0 = 1 := by
      rw [hM, Nat.gcd_comm]
      exact Nat.Coprime.pow_right _ hco
    exact perm_range M (fun i => (w0 * i) % M) (fun i _ => Nat.mod_lt _ Mpos)
      (fun i hi i' hi' hii => by
        have h3 : i % M = i' % M := Nat.ModEq.cancel_left_of_coprime hcoM hii
        rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h3)
      (fun i => φ ((i : E) / (qOf P : E) ^ a))

theorem sg_qpow {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) ∧
      Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = ((qOf P ^ f : ℕ) : K) * Sg P a b φ := by
  have hq0 := qE_ne P hp
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    rw [pow_add, mul_assoc]
    exact h1
  · show φ ((qOf P : E) ^ f * (u + δ)) = φ ((qOf P : E) ^ f * u)
    rw [mul_add]
    apply h.2
    rw [mul_div_assoc]
    exact ia_mul P (ia_qpow P _) hδ
  · have e : Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = Sg P a (b + f) φ := by
      unfold Sg
      rw [show a + f + b = a + (b + f) by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [pow_add]
      field_simp
    rw [e, sg_stab hN hp hq le_rfl (Nat.le_add_right b f) h, Nat.add_sub_cancel_left]

theorem sg_qinv {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) ∧
      Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = (qOf P : E) ^ f * ((qOf P : E) ^ a * (u / (qOf P : E) ^ f)) := by
      field_simp
    rw [e]
    exact ia_mul P (ia_qpow P _) h1
  · show φ ((u + δ) / (qOf P : E) ^ f) = φ (u / (qOf P : E) ^ f)
    rw [add_div]
    apply h.2
    have e : δ / (qOf P : E) ^ f / (qOf P : E) ^ b = δ / (qOf P : E) ^ (b + f) := by
      rw [pow_add]
      field_simp
    rw [e]
    exact hδ
  · have e : Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P (a + f) b φ := by
      unfold Sg
      rw [show a + (b + f) = a + f + b by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [pow_add]
      field_simp
    rw [e, sg_stab hN hp hq (Nat.le_add_right a f) le_rfl h, Nat.sub_self, pow_zero, Nat.cast_one, one_mul]

include hK in

theorem weighted_sum_scaling {d : E} (hd : d ≠ 0) (a b : ℕ) :
    ∃ a' b' : ℕ, ∀ φ : E → K, Good1 P a b φ →
      Good1 P a' b' (fun u => φ (d * u)) ∧ W1 P a' b' (fun u => φ (d * u)) = (qOf P : K) ^ vq P d * W1 P a b φ := by
  have hq0 := qE_ne P hp
  obtain ⟨w, hdw, hw⟩ := vq_spec hN hp hq hd
  rcases Int.eq_nat_or_neg (vq P d) with ⟨f, hf | hf⟩
  · refine ⟨a + f, b, fun φ h => ?_⟩
    have e : (fun u => φ (d * u)) = fun u => (fun u => φ ((qOf P : E) ^ f * u)) (w * u) := by
      funext u
      rw [hdw, hf, zpow_natCast, mul_assoc]
    obtain ⟨g1, s1⟩ := sg_qpow hN hp hq h f
    obtain ⟨g2, s2⟩ := sg_unit hN hp hq g1 hw
    rw [e]
    refine ⟨g2, ?_⟩
    unfold W1
    rw [s2, s1, hf, zpow_natCast]
    push_cast
    ring
  · refine ⟨a, b + f, fun φ h => ?_⟩
    have e : (fun u => φ (d * u)) = fun u => (fun u => φ (u / (qOf P : E) ^ f)) (w * u) := by
      funext u
      rw [hdw, hf, zpow_neg, zpow_natCast]
      congr 1
      field_simp
    obtain ⟨g1, s1⟩ := sg_qinv hN hp hq h f
    obtain ⟨g2, s2⟩ := sg_unit hN hp hq g1 hw
    rw [e]
    refine ⟨g2, ?_⟩
    unfold W1
    rw [s2, s1, hf, zpow_neg, zpow_natCast, pow_add]
    field_simp

end Main

end PI.TwistedEisensteinNonvanishing.W
