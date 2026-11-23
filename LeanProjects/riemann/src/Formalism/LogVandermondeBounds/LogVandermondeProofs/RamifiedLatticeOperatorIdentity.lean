import Formalism.LogVandermondeBounds.FinrankFiberSumZero

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section SlopeTestRemainingChoices

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

lemma pair_comm (f x : Fin r → k) : pair f x = pair x f := by
  unfold pair; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma pair_smul_left (c : k) (f x : Fin r → k) : pair (c • f) x = c * pair f x := by
  unfold pair; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [mul_assoc])

lemma pair_smul_right (c : k) (f x : Fin r → k) : pair f (c • x) = c * pair f x := by
  rw [pair_comm, pair_smul_left, pair_comm]

lemma pair_zero_right (f : Fin r → k) : pair f 0 = 0 := by simp [pair]

lemma pair_add_left (f g x : Fin r → k) : pair (f + g) x = pair f x + pair g x := by
  simp [pair, add_mul, Finset.sum_add_distrib]

lemma pair_single_left (i : Fin r) (t : k) (x : Fin r → k) :
    pair (Pi.single i t) x = t * x i := by
  unfold pair
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

lemma ne_zero_of_pair_eq_one {f x : Fin r → k} (h : pair f x = 1) : x ≠ 0 := by
  rintro rfl; rw [pair_zero_right] at h; exact zero_ne_one h

lemma opU_eq_opD (ψ : (Fin r → k) → R) : opU ψ = opD ψ := by
  funext f
  unfold opU opD
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pair_comm]

lemma nmP_eq_nmV (φ : (Fin r → k) → R) : nmP φ = nmV φ := by
  funext f
  unfold nmP nmV diaP diaV
  exact (Fintype.sum_equiv (Equiv.inv kˣ) (fun c => φ (((c⁻¹ : kˣ) : k) • f))
    (fun c => φ ((c : k) • f)) (fun c => rfl)).symm

lemma comm_U (c : kˣ) (ψ : (Fin r → k) → R) : opU (diaV c ψ) = diaP c (opU ψ) := by
  funext f
  unfold opU diaV diaP
  refine Finset.sum_nbij' (fun x => ((c⁻¹ : kˣ) : k) • x) (fun y => (c : k) • y) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [pair_smul_left, pair_smul_right, hx, mul_one]; exact c.mul_inv
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [pair_smul_right, ← pair_smul_left]; exact hy
  · intro x _; simp only [smul_smul, c.mul_inv, one_smul]
  · intro y _; simp only [smul_smul, c.inv_mul, one_smul]
  · intro x _; rfl

lemma comm_U_apply (c : kˣ) (ψ : (Fin r → k) → R) (f : Fin r → k) :
    opU (diaV c ψ) f = diaP c (opU ψ) f := congrFun (comm_U c ψ) f

lemma nmP_opU (ψ : (Fin r → k) → R) (f : Fin r → k) :
    nmP (opU ψ) f = ∑ x ∈ univ.filter (fun x => pair f x = 1), nmV ψ x := by
  unfold nmP
  simp only [← comm_U_apply]
  unfold opU nmV
  exact Finset.sum_comm

lemma exists_coord_ne_zero {x : Fin r → k} (hx : x ≠ 0) : ∃ i, x i ≠ 0 := by
  by_contra h
  push_neg at h
  exact hx (funext h)

lemma nmV_eq_image (ψ : (Fin r → k) → R) {x : Fin r → k} (hx : x ≠ 0) :
    nmV ψ x = ∑ y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x), ψ y := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
  unfold nmV diaV
  rw [Finset.sum_image]
  intro c _ d _ h
  have h' := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at h'
  have h'' : ((c⁻¹ : kˣ) : k) = ((d⁻¹ : kˣ) : k) := mul_right_cancel₀ hi h'
  exact inv_inj.1 (Units.ext h'')

lemma mem_image_orbit {x : Fin r → k} (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ ∃ u : kˣ, u • x = y := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by rw [Units.smul_def]⟩
  · rintro ⟨u, rfl⟩; exact ⟨u⁻¹, by rw [inv_inv, Units.smul_def]⟩

lemma mem_image_line {x : Fin r → k} (hx : x ≠ 0) (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ y ≠ 0 ∧ ∃ c : k, y = c • x := by
  rw [mem_image_orbit]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ⟨(u : k), Units.smul_def u x⟩⟩
    intro h0
    apply hx
    have h1 := congrArg (fun z => ((u⁻¹ : kˣ) : k) • z) h0
    simp only [smul_zero] at h1
    rw [Units.smul_def, smul_smul, u.inv_mul, one_smul] at h1
    exact h1
  · rintro ⟨hy, c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; exact hy (zero_smul _ _)
    exact ⟨Units.mk0 c hc, by rw [Units.smul_def, Units.val_mk0]⟩

lemma trV_eq_zero (ψ : (Fin r → k) → R) (h : ∀ y, y ≠ 0 → nmV ψ y = 0) : trV ψ = 0 := by
  classical
  let π : (Fin r → k) → Quotient (MulAction.orbitRel kˣ (Fin r → k)) := Quotient.mk _
  unfold trV
  rw [← Finset.sum_fiberwise_of_maps_to (g := π)
    (t := (univ.filter (fun x : Fin r → k => x ≠ 0)).image π)
    (fun x hx => Finset.mem_image_of_mem π hx)]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0
  have hfib : (univ.filter (fun x : Fin r → k => x ≠ 0)).filter (fun x => π x = π x0) =
      univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x0) := by
    ext y
    rw [mem_image_orbit]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, π, Quotient.eq,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨_, hu⟩
      exact hu
    · rintro ⟨u, rfl⟩
      refine ⟨?_, ⟨u, rfl⟩⟩
      intro h0
      apply hx0
      have h1 := congrArg (fun z => u⁻¹ • z) h0
      simp only [smul_zero, smul_smul, inv_mul_cancel, one_smul] at h1
      exact h1
  rw [hfib, ← nmV_eq_image ψ hx0]
  exact h x0 hx0

lemma card_fiber_mul (W : Type*) [AddCommGroup W] [Fintype W] [DecidableEq W]
    (L : (Fin r → k) →+ W) (hL : Function.Surjective L) (w : W) :
    (univ.filter (fun f => L f = w)).card * Fintype.card W = Fintype.card k ^ r := by
  have hfib : ∀ w, (univ.filter (fun f => L f = w)).card =
      (univ.filter (fun f => L f = 0)).card := by
    intro w
    obtain ⟨f0, hf0⟩ := hL w
    refine Finset.card_nbij' (fun f => f - f0) (fun f => f + f0) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
      rw [map_sub, hf, hf0, sub_self]
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
      rw [map_add, hf, hf0, zero_add]
    · intro f _; simp
    · intro f _; simp
  have htot := Finset.card_eq_sum_card_fiberwise (f := L) (s := (univ : Finset (Fin r → k)))
    (t := univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, smul_eq_mul] at htot
  have hcard : Fintype.card (Fin r → k) = Fintype.card k ^ r := by simp
  rw [Finset.card_univ, Finset.card_univ] at htot
  rw [hfib w, ← hcard, htot, Nat.mul_comm]

def pairL (x : Fin r → k) : (Fin r → k) →+ k where
  toFun f := pair f x
  map_zero' := by simp [pair]
  map_add' f g := pair_add_left f g x

lemma pairL_apply (x f : Fin r → k) : pairL x f = pair f x := rfl

def pairTwoLinear (x y : Fin r → k) : (Fin r → k) →+ k × k where
  toFun f := (pair f x, pair f y)
  map_zero' := by simp [pair]
  map_add' f g := by simp [pair_add_left]

lemma pairTwoLinear_apply (x y f : Fin r → k) : pairTwoLinear x y f = (pair f x, pair f y) := rfl

lemma count1 {x : Fin r → k} (hx : x ≠ 0) (a : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a)).card = Fintype.card k ^ (r - 1) := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
  have hL : Function.Surjective (pairL x) := fun a =>
    ⟨Pi.single i (a / x i), by rw [pairL_apply, pair_single_left, div_mul_cancel₀ _ hi]⟩
  have h := card_fiber_mul k (pairL x) hL a
  have hq : 0 < Fintype.card k := Fintype.card_pos
  have hr : r - 1 + 1 = r := by have := i.pos; omega
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← pow_succ, hr]
  exact h

lemma count2 (hr : 2 ≤ r) {x y : Fin r → k} (hx : x ≠ 0) (hy : ∀ c : k, y ≠ c • x) (a b : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b)).card =
      Fintype.card k ^ (r - 2) := by
  have hminor : ∃ i j, x i * y j - x j * y i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
    apply hy (y i / x i)
    funext j
    have := hcon i j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi]
    linear_combination this
  obtain ⟨i, j, hD⟩ := hminor
  have hL : Function.Surjective (pairTwoLinear x y) := by
    rintro ⟨a, b⟩
    refine ⟨Pi.single i ((a * y j - b * x j) / (x i * y j - x j * y i)) +
      Pi.single j ((b * x i - a * y i) / (x i * y j - x j * y i)), ?_⟩
    rw [pairTwoLinear_apply, pair_add_left, pair_add_left, pair_single_left, pair_single_left,
      pair_single_left, pair_single_left]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
    · dsimp only
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
  have h := card_fiber_mul (k × k) (pairTwoLinear x y) hL (a, b)
  have hfil : univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b) =
      univ.filter (fun f => pairTwoLinear x y f = (a, b)) := by
    ext f; simp [pairTwoLinear_apply]
  rw [hfil]
  have hq : 0 < Fintype.card k * Fintype.card k := Nat.mul_pos Fintype.card_pos Fintype.card_pos
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [Fintype.card_prod] at h
  rw [h, ← mul_assoc, ← pow_succ, ← pow_succ]
  congr 1; omega

lemma DU_formula (hr : 2 ≤ r) (ψ : (Fin r → k) → R) (x : Fin r → k) (hx : x ≠ 0) :
    opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x
      - ((Fintype.card k : R)) ^ (r - 2) * nmV ψ x + ((Fintype.card k : R)) ^ (r - 2) * trV ψ := by
  have h1 : opD (opU ψ) x = ∑ y, ((univ.filter (fun f : Fin r → k =>
      pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y := by
    unfold opD opU
    rw [Finset.sum_comm' (t' := univ)
      (s' := fun y => univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1))]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro f y; simp
  have h2 : ∀ y, ((univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y =
      (if y = x then ((Fintype.card k : R)) ^ (r - 1) * ψ y else 0) +
      (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) := by
    intro y
    by_cases hyx : y = x
    · rw [hyx]
      have hne : ¬ ∀ c : k, x ≠ c • x := fun h => h 1 (one_smul _ _).symm
      rw [if_pos rfl, if_neg hne, add_zero]
      have : univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f x = 1) =
          univ.filter (fun f => pair f x = 1) := by
        ext f; simp
      rw [this, count1 hx 1]; push_cast; ring
    · rw [if_neg hyx]
      by_cases hl : ∀ c : k, y ≠ c • x
      · rw [if_pos hl, zero_add, count2 hr hx hl 1 1]; push_cast; ring
      · rw [if_neg hl]
        push_neg at hl
        obtain ⟨c, rfl⟩ := hl
        have hc : c ≠ 1 := by rintro rfl; exact hyx (one_smul _ _)
        rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun f _ h =>
          hc (by rw [← h.2, pair_smul_right, h.1, mul_one])))]
        simp
  have htr : trV ψ = nmV ψ x + ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y := by
    unfold trV
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun y : Fin r → k => y ≠ 0))
      (fun y => ∃ c : k, y = c • x)]
    congr 1
    · rw [nmV_eq_image ψ hx]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      rw [mem_image_line hx]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, ne_eq]
      exact ⟨fun h => h.2, fun h => ⟨fun h0 => h 0 (by simp [h0]), h⟩⟩
  rw [h1, Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), htr]
  have h3 : ∑ y, (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) =
      ((Fintype.card k : R)) ^ (r - 2) * ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y := by
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [h3]; ring

end SlopeTestRemainingChoices

theorem up_down_operators_adjoint : AdjointReformulated := by
  intro k _ _ _ r R _ ψ φ
  unfold opU opD
  simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun f _ => ?_))
  split_ifs <;> ring

theorem down_up_composition_formula : DualCompositionReformulated :=
  fun _ _ _ _ _ _ _ hr ψ x hx => DU_formula hr ψ x hx

theorem up_down_composition_formula : CompositionWithDual := by
  intro k _ _ _ r R _ hr φ f hf
  rw [← opU_eq_opD φ, opU_eq_opD (opU φ), nmP_eq_nmV]
  exact DU_formula hr φ f hf

lemma ram_V {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
    (ψ : (Fin r → k) → R) (h : ∀ y, y ≠ 0 → nmV ψ y = 0) :
    (∀ f, nmP (opU ψ) f = 0) ∧ trV ψ = 0 ∧
      (2 ≤ r → ∀ x, x ≠ 0 → opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x) := by
  have htr := trV_eq_zero ψ h
  refine ⟨fun f => ?_, htr, fun hr x hx => ?_⟩
  · rw [nmP_opU]
    exact Finset.sum_eq_zero (fun x hx =>
      h x (ne_zero_of_pair_eq_one (by simpa using hx)))
  · rw [DU_formula hr ψ x hx, h x hx, htr]; ring

theorem ramified_lattice_operator_identity : UnitsSumZero := by
  intro k _ _ _ r R _
  refine ⟨fun ψ h => ram_V ψ h, fun φ h => ?_⟩
  have h' : ∀ y, y ≠ 0 → nmV φ y = 0 := fun y hy => by rw [← nmP_eq_nmV]; exact h y hy
  obtain ⟨h1, h2, h3⟩ := ram_V φ h'
  refine ⟨fun x => ?_, h2, fun hr f hf => ?_⟩
  · rw [← nmP_eq_nmV, ← opU_eq_opD]; exact h1 x
  · rw [← opU_eq_opD φ, opU_eq_opD (opU φ)]; exact h3 hr f hf

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
