import Mathlib
import Formalism.UnipotentAdelicQuotients.GordanCones

set_option autoImplicit false

namespace GordanGenProof

open Finset

def gcone {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) : Set (Fin n → ℚ) :=
  {x | ∃ c : ι → ℚ, (∀ i ∈ s, 0 ≤ c i) ∧ x = ∑ i ∈ s, c i • f i}

def hcone {n : ℕ} {ι : Type*} (A : Finset ι) (f : ι → Fin n → ℚ) : Set (Fin n → ℚ) :=
  {x | ∀ a ∈ A, 0 ≤ f a ⬝ᵥ x}

theorem gcone_sub {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) (X : Set (Fin n → ℚ))
    (h0 : (0 : Fin n → ℚ) ∈ X) (hadd : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ X)
    (hsmul : ∀ r : ℚ, 0 ≤ r → ∀ x ∈ X, r • x ∈ X) (hf : ∀ i ∈ s, f i ∈ X) :
    gcone s f ⊆ X := by
  rintro x ⟨c, hc, rfl⟩
  exact Finset.sum_induction _ (· ∈ X) (fun a b ha hb => hadd a ha b hb) h0
    (fun i hi => hsmul _ (hc i hi) _ (hf i hi))

theorem zero_mem_gcone {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) :
    (0 : Fin n → ℚ) ∈ gcone s f :=
  ⟨0, fun _ _ => le_rfl, by simp⟩

theorem mem_gcone {n : ℕ} {ι : Type*} {s : Finset ι} {f : ι → Fin n → ℚ} {i : ι} (hi : i ∈ s) :
    f i ∈ gcone s f := by
  classical
  refine ⟨fun j => if j = i then 1 else 0, fun j _ => ?_, ?_⟩
  · by_cases h : j = i <;> simp [h]
  · simp [ite_smul, hi]

theorem mem_gcone_insert {n : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → Fin n → ℚ}
    {w : ι} (hw : w ∉ s) (x : Fin n → ℚ) :
    x ∈ gcone (insert w s) f ↔ ∃ t : ℚ, 0 ≤ t ∧ x - t • f w ∈ gcone s f := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c w, hc w (Finset.mem_insert_self w s), c, fun i hi => hc i (Finset.mem_insert_of_mem hi), ?_⟩
    rw [Finset.sum_insert hw]
    abel
  · rintro ⟨t, ht, c, hc, hx⟩
    refine ⟨fun j => if j = w then t else c j, fun i hi => ?_, ?_⟩
    · rcases Finset.mem_insert.1 hi with h | h
      · subst h
        show 0 ≤ (if i = i then t else c i)
        rw [if_pos rfl]
        exact ht
      · show 0 ≤ (if i = w then t else c i)
        rw [if_neg (ne_of_mem_of_not_mem h hw)]
        exact hc i h
    · show x = ∑ j ∈ insert w s, (if j = w then t else c j) • f j
      rw [Finset.sum_insert hw, if_pos rfl]
      have hs : ∑ j ∈ s, (if j = w then t else c j) • f j = ∑ j ∈ s, c j • f j :=
        Finset.sum_congr rfl fun j hj => by rw [if_neg (ne_of_mem_of_not_mem hj hw)]
      rw [hs, ← hx]
      abel

theorem fm_scalar {κ : Type*} (P : Finset κ) (u c : κ → ℚ) :
    (∃ t : ℚ, ∀ p ∈ P, 0 ≤ u p + c p * t) ↔
      (∀ p ∈ P, c p = 0 → 0 ≤ u p) ∧
      (∀ p ∈ P, ∀ q ∈ P, 0 < c p → c q < 0 → 0 ≤ c p * u q - c q * u p) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun p hp hc => by simpa [hc] using ht p hp, fun p hp q hq hcp hcq => ?_⟩
    have h1 := ht p hp
    have h2 := ht q hq
    nlinarith [mul_nonneg (neg_nonneg.2 hcq.le) h1, mul_nonneg hcp.le h2]
  · rintro ⟨h0, h1⟩
    obtain ⟨b, eb⟩ : ∃ b : κ → ℚ, ∀ p, c p ≠ 0 → c p * b p = -u p :=
      ⟨fun p => -u p * (c p)⁻¹, fun p hp => by
        show c p * (-u p * (c p)⁻¹) = -u p
        rw [mul_left_comm, mul_inv_cancel₀ hp, mul_one]⟩
    have key : ∀ p ∈ P, ∀ q ∈ P, 0 < c p → c q < 0 → b p ≤ b q := by
      intro p hp q hq hcp hcq
      by_contra hlt
      push_neg at hlt
      have e1 : c p * b p * c q = -u p * c q := by rw [eb p hcp.ne']
      have e2 : c q * b q * c p = -u q * c p := by rw [eb q hcq.ne]
      have hm := mul_pos (mul_pos hcp (neg_pos.2 hcq)) (sub_pos.2 hlt)
      have h3 := h1 p hp q hq hcp hcq
      nlinarith
    have good : ∀ t : ℚ, (∀ p ∈ P, 0 < c p → b p ≤ t) → (∀ q ∈ P, c q < 0 → t ≤ b q) →
        ∀ p ∈ P, 0 ≤ u p + c p * t := by
      intro t hlo hhi p hp
      rcases lt_trichotomy (c p) 0 with hn | hz | hpos
      · have h4 := mul_le_mul_of_nonpos_left (hhi p hp hn) hn.le
        rw [eb p hn.ne] at h4
        linarith
      · rw [hz, zero_mul, add_zero]
        exact h0 p hp hz
      · have h4 := mul_le_mul_of_nonneg_left (hlo p hp hpos) hpos.le
        rw [eb p hpos.ne'] at h4
        linarith
    by_cases hL : ∃ p ∈ P, 0 < c p
    · obtain ⟨p0, hp0, hcp0, hmax⟩ : ∃ p0 ∈ P, 0 < c p0 ∧ ∀ p ∈ P, 0 < c p → b p ≤ b p0 := by
        obtain ⟨p, hp, hc⟩ := hL
        have hne : (P.filter (fun p => 0 < c p)).Nonempty := ⟨p, Finset.mem_filter.2 ⟨hp, hc⟩⟩
        obtain ⟨p0, hp0, hm⟩ := Finset.exists_max_image _ b hne
        rw [Finset.mem_filter] at hp0
        exact ⟨p0, hp0.1, hp0.2, fun p hp hc => hm p (Finset.mem_filter.2 ⟨hp, hc⟩)⟩
      exact ⟨b p0, good _ hmax (fun q hq hcq => key p0 hp0 q hq hcp0 hcq)⟩
    · push_neg at hL
      by_cases hU : ∃ q ∈ P, c q < 0
      · obtain ⟨q0, hq0, hcq0, hmin⟩ : ∃ q0 ∈ P, c q0 < 0 ∧ ∀ q ∈ P, c q < 0 → b q0 ≤ b q := by
          obtain ⟨q, hq, hc⟩ := hU
          have hne : (P.filter (fun q => c q < 0)).Nonempty := ⟨q, Finset.mem_filter.2 ⟨hq, hc⟩⟩
          obtain ⟨q0, hq0, hm⟩ := Finset.exists_min_image _ b hne
          rw [Finset.mem_filter] at hq0
          exact ⟨q0, hq0.1, hq0.2, fun q hq hc => hm q (Finset.mem_filter.2 ⟨hq, hc⟩)⟩
        exact ⟨b q0, good _ (fun p hp hcp => absurd hcp (not_lt.2 (hL p hp))) hmin⟩
      · push_neg at hU
        exact ⟨0, good 0 (fun p hp hcp => absurd hcp (not_lt.2 (hL p hp)))
          (fun q hq hcq => absurd hcq (not_lt.2 (hU q hq)))⟩

def fmSet {n : ℕ} (P : Finset ((Fin n → ℚ) × ℚ)) : Finset (Fin n → ℚ) :=
  (P.filter (fun p => p.2 = 0)).image Prod.fst ∪
    ((P.filter (fun p => 0 < p.2)) ×ˢ (P.filter (fun p => p.2 < 0))).image
      (fun pq => pq.1.2 • pq.2.1 - pq.2.2 • pq.1.1)

theorem fm_dot {n : ℕ} (a b : ℚ) (u v x : Fin n → ℚ) :
    (a • u - b • v) ⬝ᵥ x = a * (u ⬝ᵥ x) - b * (v ⬝ᵥ x) := by
  show ∑ i, (a • u - b • v) i * x i = a * ∑ i, u i * x i - b * ∑ i, v i * x i
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem fm_vec {n : ℕ} (P : Finset ((Fin n → ℚ) × ℚ)) (x : Fin n → ℚ) :
    (∃ t : ℚ, ∀ p ∈ P, 0 ≤ p.1 ⬝ᵥ x + p.2 * t) ↔ x ∈ hcone (fmSet P) id := by
  refine (fm_scalar P (fun p => p.1 ⬝ᵥ x) (fun p => p.2)).trans ?_
  constructor
  · rintro ⟨h0, h1⟩
    show ∀ a ∈ fmSet P, 0 ≤ id a ⬝ᵥ x
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      rw [Finset.mem_filter] at hp
      exact h0 p hp.1 hp.2
    · obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 ha
      simp only [Finset.mem_product, Finset.mem_filter] at hpq
      show 0 ≤ (p.2 • q.1 - q.2 • p.1) ⬝ᵥ x
      rw [fm_dot]
      exact h1 p hpq.1.1 q hpq.2.1 hpq.1.2 hpq.2.2
  · intro h
    have h' : ∀ a ∈ fmSet P, 0 ≤ a ⬝ᵥ x := h
    refine ⟨fun p hp hz => h' p.1 (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hp, hz⟩))), fun p hp q hq hcp hcq => ?_⟩
    have h2 := h' (p.2 • q.1 - q.2 • p.1) (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨(p, q), Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hp, hcp⟩, Finset.mem_filter.2 ⟨hq, hcq⟩⟩, rfl⟩))
    rw [fm_dot] at h2
    exact h2

def stdIneq (n : ℕ) : Finset (Fin n → ℚ) :=
  (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → ℚ)) ∪
    (Finset.univ.image fun i : Fin n => -(Pi.single i 1 : Fin n → ℚ))

private theorem rat_dotProduct_zero_right {n : ℕ} (a : Fin n → ℚ) : a ⬝ᵥ (0 : Fin n → ℚ) = 0 := by
  show ∑ j, a j * (0 : Fin n → ℚ) j = 0
  simp

theorem mem_hcone_stdIneq (n : ℕ) (x : Fin n → ℚ) : x ∈ hcone (stdIneq n) id ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have h1 : 0 ≤ (Pi.single i (1 : ℚ) : Fin n → ℚ) ⬝ᵥ x :=
      h (Pi.single i 1) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have h2 : 0 ≤ (-(Pi.single i (1 : ℚ)) : Fin n → ℚ) ⬝ᵥ x :=
      h (-(Pi.single i 1)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have e1 : (Pi.single i (1 : ℚ) : Fin n → ℚ) ⬝ᵥ x = x i := by
      show ∑ j, (Pi.single i (1 : ℚ) : Fin n → ℚ) j * x j = x i
      simp [Pi.single_apply]
    have e2 : (-(Pi.single i (1 : ℚ)) : Fin n → ℚ) ⬝ᵥ x = -x i := by
      rw [← e1]
      show ∑ j, (-(Pi.single i (1 : ℚ)) : Fin n → ℚ) j * x j = -∑ j, (Pi.single i (1 : ℚ) : Fin n → ℚ) j * x j
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => neg_mul _ _
    rw [e1] at h1
    rw [e2] at h2
    show x i = 0
    exact le_antisymm (by linarith) h1
  · rintro rfl
    show ∀ a ∈ stdIneq n, 0 ≤ id a ⬝ᵥ (0 : Fin n → ℚ)
    intro a _
    exact le_of_eq (rat_dotProduct_zero_right _).symm

theorem mem_gcone_empty {n : ℕ} (x : Fin n → ℚ) :
    x ∈ gcone (∅ : Finset (Fin n → ℚ)) id ↔ x = 0 := by
  constructor
  · rintro ⟨c, -, hx⟩
    simpa using hx
  · rintro rfl
    exact zero_mem_gcone _ _

private theorem rat_dotProduct_zero_left {n : ℕ} (x : Fin n → ℚ) : (0 : Fin n → ℚ) ⬝ᵥ x = 0 := by
  show ∑ j, (0 : Fin n → ℚ) j * x j = 0
  simp

private theorem rat_dotProduct_sub_smul_right {n : ℕ} (a x w : Fin n → ℚ) (t : ℚ) :
    a ⬝ᵥ (x - t • w) = a ⬝ᵥ x - t * (a ⬝ᵥ w) := by
  show ∑ j, a j * (x - t • w) j = ∑ j, a j * x j - t * ∑ j, a j * w j
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem minkowskiQ {n : ℕ} (T : Finset (Fin n → ℚ)) :
    ∃ A : Finset (Fin n → ℚ), gcone T id = hcone A id := by
  refine Finset.induction_on T ?_ ?_
  · exact ⟨stdIneq n, Set.ext fun x => by
      rw [mem_gcone_empty, mem_hcone_stdIneq]⟩
  · intro w T hw ih
    obtain ⟨A, hA⟩ := ih
    refine ⟨fmSet (A.image (fun a => (a, -(a ⬝ᵥ w))) ∪ {((0 : Fin n → ℚ), (1 : ℚ))}),
      Set.ext fun x => ?_⟩
    rw [← fm_vec, mem_gcone_insert hw, hA]
    refine exists_congr fun t => ?_
    constructor
    · rintro ⟨ht, h⟩ p hp
      rcases Finset.mem_union.1 hp with hp | hp
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
        have h1 : 0 ≤ a ⬝ᵥ (x - t • w) := h a ha
        rw [rat_dotProduct_sub_smul_right] at h1
        show 0 ≤ a ⬝ᵥ x + -(a ⬝ᵥ w) * t
        have e : -(a ⬝ᵥ w) * t = -(t * (a ⬝ᵥ w)) := by ring
        rw [e]
        linarith
      · rw [Finset.mem_singleton.1 hp]
        show 0 ≤ (0 : Fin n → ℚ) ⬝ᵥ x + 1 * t
        rw [rat_dotProduct_zero_left, one_mul, zero_add]
        exact ht
    · intro h
      have ht : 0 ≤ t := by
        have h0 := h ((0 : Fin n → ℚ), (1 : ℚ)) (Finset.mem_union_right _ (Finset.mem_singleton_self _))
        have h0' : 0 ≤ (0 : Fin n → ℚ) ⬝ᵥ x + 1 * t := h0
        rw [rat_dotProduct_zero_left, one_mul, zero_add] at h0'
        exact h0'
      refine ⟨ht, ?_⟩
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (x - t • id w)
      intro a ha
      have h2 := h (a, -(a ⬝ᵥ w)) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
      have h2' : 0 ≤ a ⬝ᵥ x + -(a ⬝ᵥ w) * t := h2
      show 0 ≤ a ⬝ᵥ (x - t • w)
      rw [rat_dotProduct_sub_smul_right]
      have e : -(a ⬝ᵥ w) * t = -(t * (a ⬝ᵥ w)) := by ring
      rw [e] at h2'
      linarith

private theorem rat_dotProduct_comm {n : ℕ} (a b : Fin n → ℚ) : a ⬝ᵥ b = b ⬝ᵥ a := by
  show ∑ j, a j * b j = ∑ j, b j * a j
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem rat_dotProduct_add_left {n : ℕ} (a b x : Fin n → ℚ) : (a + b) ⬝ᵥ x = a ⬝ᵥ x + b ⬝ᵥ x := by
  show ∑ j, (a + b) j * x j = ∑ j, a j * x j + ∑ j, b j * x j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => add_mul (a j) (b j) (x j)

private theorem rat_dotProduct_add_right {n : ℕ} (a x y : Fin n → ℚ) : a ⬝ᵥ (x + y) = a ⬝ᵥ x + a ⬝ᵥ y := by
  show ∑ j, a j * (x + y) j = ∑ j, a j * x j + ∑ j, a j * y j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => mul_add (a j) (x j) (y j)

private theorem rat_dotProduct_smul_left {n : ℕ} (r : ℚ) (a x : Fin n → ℚ) : (r • a) ⬝ᵥ x = r * (a ⬝ᵥ x) := by
  show ∑ j, (r • a) j * x j = r * ∑ j, a j * x j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc r (a j) (x j)

private theorem rat_dotProduct_smul_right {n : ℕ} (r : ℚ) (a x : Fin n → ℚ) : a ⬝ᵥ (r • x) = r * (a ⬝ᵥ x) := by
  show ∑ j, a j * (r • x) j = r * ∑ j, a j * x j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_left_comm (a j) r (x j)

private theorem dotProduct_nonneg_of_mem_hcone_of_mem_gcone {n : ℕ} {A : Finset (Fin n → ℚ)} {x d : Fin n → ℚ}
    (hx : x ∈ hcone A id) (hd : d ∈ gcone A id) : 0 ≤ d ⬝ᵥ x := by
  have hsub : gcone A id ⊆ {e | 0 ≤ e ⬝ᵥ x} :=
    gcone_sub A id _
      (by show 0 ≤ (0 : Fin n → ℚ) ⬝ᵥ x; exact le_of_eq (rat_dotProduct_zero_left x).symm)
      (fun a ha b hb => by
        have ha' : 0 ≤ a ⬝ᵥ x := ha
        have hb' : 0 ≤ b ⬝ᵥ x := hb
        show 0 ≤ (a + b) ⬝ᵥ x
        rw [rat_dotProduct_add_left]
        exact add_nonneg ha' hb')
      (fun r hr a ha => by
        have ha' : 0 ≤ a ⬝ᵥ x := ha
        show 0 ≤ (r • a) ⬝ᵥ x
        rw [rat_dotProduct_smul_left]
        exact mul_nonneg hr ha')
      (fun a ha => hx a ha)
  exact hsub hd

theorem weylQ {n : ℕ} (A : Finset (Fin n → ℚ)) :
    ∃ B : Finset (Fin n → ℚ), hcone A id = gcone B id := by
  obtain ⟨B, hB⟩ := minkowskiQ A
  obtain ⟨D, hD⟩ := minkowskiQ B
  refine ⟨B, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    rw [hD]
    show ∀ d ∈ D, 0 ≤ id d ⬝ᵥ x
    intro d hd
    have hdA : d ∈ gcone A id := by
      rw [hB]
      show ∀ b ∈ B, 0 ≤ id b ⬝ᵥ d
      intro b hb
      have hb' : id b ∈ gcone B id := mem_gcone hb
      rw [hD] at hb'
      have h2 : 0 ≤ id d ⬝ᵥ id b := hb' d hd
      show 0 ≤ b ⬝ᵥ d
      rw [rat_dotProduct_comm]
      exact h2
    exact dotProduct_nonneg_of_mem_hcone_of_mem_gcone hx hdA
  · refine gcone_sub B id _ ?_ ?_ ?_ ?_
    · show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (0 : Fin n → ℚ)
      intro a _
      exact le_of_eq (rat_dotProduct_zero_right _).symm
    · intro x hx y hy
      have hx' : ∀ a ∈ A, 0 ≤ id a ⬝ᵥ x := hx
      have hy' : ∀ a ∈ A, 0 ≤ id a ⬝ᵥ y := hy
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (x + y)
      intro a ha
      rw [rat_dotProduct_add_right]
      exact add_nonneg (hx' a ha) (hy' a ha)
    · intro r hr x hx
      have hx' : ∀ a ∈ A, 0 ≤ id a ⬝ᵥ x := hx
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ (r • x)
      intro a ha
      rw [rat_dotProduct_smul_right]
      exact mul_nonneg hr (hx' a ha)
    · intro b hb
      show ∀ a ∈ A, 0 ≤ id a ⬝ᵥ id b
      intro a ha
      have h1 : id a ∈ gcone A id := mem_gcone ha
      rw [hB] at h1
      have h2 : 0 ≤ id b ⬝ᵥ id a := h1 b hb
      rw [rat_dotProduct_comm]
      exact h2

theorem exists_int_multiple {n : ℕ} (v : Fin n → ℚ) :
    ∃ N : ℚ, 0 < N ∧ ∃ z : Fin n → ℤ, GordanCones.toQ z = N • v := by
  classical
  have hden : ∀ q : ℚ, 0 < q.den := fun q => q.den_pos
  have key : ∀ q : ℚ, q * (q.den : ℚ) = (q.num : ℚ) := fun q => Rat.mul_den_eq_num q
  refine ⟨∏ j, ((v j).den : ℚ), Finset.prod_pos fun j _ => by exact_mod_cast hden (v j),
    fun i => (v i).num * ∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ), ?_⟩
  funext i
  show ((((v i).num * ∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ) : ℤ)) : ℚ) =
    (∏ j, ((v j).den : ℚ)) * v i
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ((v j).den : ℚ)) (Finset.mem_univ i)]
  push_cast
  rw [← key (v i)]
  ring

noncomputable def intOf {n : ℕ} (v : Fin n → ℚ) : Fin n → ℤ :=
  (exists_int_multiple v).choose_spec.2.choose

noncomputable def mulOf {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  (exists_int_multiple v).choose

theorem mulOf_pos {n : ℕ} (v : Fin n → ℚ) : 0 < mulOf v :=
  (exists_int_multiple v).choose_spec.1

theorem toQ_intOf {n : ℕ} (v : Fin n → ℚ) : GordanCones.toQ (intOf v) = mulOf v • v :=
  (exists_int_multiple v).choose_spec.2.choose_spec

end GordanGenProof
