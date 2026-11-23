import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICKoszul

open CompanionTheory.D.DSIC

section Ring

variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem homotopy_ring (A D an cr : ι → R)
    (h1 : ∀ i j, Commute (an i) (D j)) (h2 : ∀ i j, Commute (cr i) (A j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0)
    (h4 : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, A i * an i) * (∑ j, D j * cr j) + (∑ j, D j * cr j) * (∑ i, A i * an i) =
      ∑ i, A i * D i + ∑ i, cr i * an i := by
  have key : ∀ i j, A i * an i * (D j * cr j) + D j * cr j * (A i * an i) =
      (if i = j then A i * D i else 0) + (if i = j then cr i * an i else 0) := by
    intro i j
    have e1 : A i * an i * (D j * cr j) = A i * D j * (an i * cr j) := by
      rw [mul_assoc, ← mul_assoc (an i), (h1 i j).eq, mul_assoc, mul_assoc]
    have e2 : D j * cr j * (A i * an i) = D j * A i * (cr j * an i) := by
      rw [mul_assoc, ← mul_assoc (cr j), (h2 j i).eq, mul_assoc, mul_assoc]
    have e3 : D j * A i = A i * D j + if j = i then 1 else 0 := by
      rw [← h3 j i]; abel
    rw [e1, e2, e3, add_mul, ← add_assoc, ← mul_add, h4]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := univ) (t := univ)
    (f := fun j i => D j * cr j * (A i * an i)), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp only [key, Finset.sum_add_distrib]
  simp

omit [DecidableEq ι] in

theorem sq_ring (A an : ι → R)
    (h1 : ∀ i j, Commute (an i) (A j)) (h2 : ∀ i j, Commute (A i) (A j))
    (h4 : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, A i * an i) * (∑ j, A j * an j) + (∑ j, A j * an j) * (∑ i, A i * an i) = 0 := by
  have key : ∀ i j, A i * an i * (A j * an j) + A j * an j * (A i * an i) = 0 := by
    intro i j
    have e1 : A i * an i * (A j * an j) = A i * A j * (an i * an j) := by
      rw [mul_assoc, ← mul_assoc (an i), (h1 i j).eq, mul_assoc, mul_assoc]
    have e2 : A j * an j * (A i * an i) = A j * A i * (an j * an i) := by
      rw [mul_assoc, ← mul_assoc (an j), (h1 j i).eq, mul_assoc, mul_assoc]
    rw [e1, e2, (h2 j i).eq, ← mul_add, h4, mul_zero]
  conv_lhs => congr; rw [Finset.sum_mul_sum]; rfl; rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => key i j

theorem euler_ring (A D : ι → R) (h2 : ∀ i j, Commute (D i) (D j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0) (i : ι) :
    D i * (∑ j, A j * D j) = (∑ j, A j * D j) * D i + D i := by
  have key : ∀ j, D i * (A j * D j) = A j * D j * D i + if i = j then D i else 0 := by
    intro j
    have e3 : D i * A j = A j * D i + if i = j then 1 else 0 := by
      rw [← h3 i j]; abel
    rw [← mul_assoc, e3, add_mul, mul_assoc, (h2 i j).eq, ← mul_assoc]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [key, Finset.sum_add_distrib]
  simp

end Ring

section Filt

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}

def filt (d : ι → Module.End ℂ Z) (m : ℕ) : Submodule ℂ Z :=
  Nat.rec (motive := fun _ => Submodule ℂ Z) ⊥ (fun _ S => ⨅ i, S.comap (d i)) m

theorem mem_filt_succ (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z) :
    z ∈ filt d (m + 1) ↔ ∀ i, d i z ∈ filt d m := by
  show z ∈ (⨅ i, (filt d m).comap (d i)) ↔ _
  simp [Submodule.mem_iInf]

theorem filt_mono (d : ι → Module.End ℂ Z) : Monotone (filt d) := by
  refine monotone_nat_of_le_succ fun m => ?_
  induction m with
  | zero => exact bot_le
  | succ m ih =>
    intro z hz
    rw [mem_filt_succ] at hz ⊢
    exact fun i => ih (hz i)

theorem mem_filt_of_words (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z)
    (h : ∀ l : List ι, l.length = m → (l.map d).prod z = 0) : z ∈ filt d m := by
  induction m generalizing z with
  | zero => simpa [filt] using h [] rfl
  | succ m ih =>
    rw [mem_filt_succ]
    intro i
    refine ih _ fun l hl => ?_
    have := h (l ++ [i]) (by simp [hl])
    simpa using this

theorem euler_filt [Fintype ι] [DecidableEq ι] (a d : ι → Module.End ℂ Z) (h2 : ∀ i j, Commute (d i) (d j))
    (h3 : ∀ i j, d i * a j - a j * d i = if i = j then 1 else 0) (m : ℕ) (z : Z)
    (hz : z ∈ filt d (m + 1)) : (∑ j, a j * d j) z - (m : ℂ) • z ∈ filt d m := by
  induction m generalizing z with
  | zero =>
    rw [mem_filt_succ] at hz
    have h0 : ∀ i, d i z = 0 := fun i => by simpa [filt] using hz i
    simp [filt, LinearMap.sum_apply, h0]
  | succ m ih =>
    rw [mem_filt_succ] at hz ⊢
    intro i
    have e := congrArg (fun T : Module.End ℂ Z => T z) (euler_ring a d h2 h3 i)
    simp only [Module.End.mul_apply, LinearMap.add_apply] at e
    have := ih _ (hz i)
    convert this using 1
    rw [map_sub, e, map_smul]
    push_cast
    rw [add_smul, one_smul]
    abel

end Filt

variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem lift_mul (S T : Module.End ℂ Z) :
    (lift ε (S * T) : Module.End ℂ (Ch ε Z)) = lift ε S * lift ε T := rfl

theorem ann_lift (i : NC ε) (T : Module.End ℂ Z) :
    Commute (ann i : Module.End ℂ (Ch ε Z)) (lift ε T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [ann, h]

theorem cre_lift (i : NC ε) (T : Module.End ℂ Z) :
    Commute (cre i : Module.End ℂ (Ch ε Z)) (lift ε T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [cre, h]

theorem cre_ann_apply (i : NC ε) (x : Ch ε Z) (A : Finset (NC ε)) :
    (cre i (ann i x)) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · have e : sg i (A.erase i) = sg i A := by
      unfold sg
      congr 2
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨fun hh => by rw [hh] at h2; exact lt_irrefl _ h2, h1⟩, h2⟩
    have e2 : sg i A * sg i A = 1 := by
      unfold sg
      rw [← mul_pow]; simp
    simp [cre, ann, h, e, Finset.insert_erase h, smul_smul, e2]
  · simp [cre, h]

theorem number_apply (x : Ch ε Z) (A : Finset (NC ε)) :
    ((∑ i : NC ε, (cre i * ann i : Module.End ℂ (Ch ε Z))) x) A = (A.card : ℂ) • x A := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [Module.End.mul_apply, cre_ann_apply]
  rw [← Finset.sum_filter]
  simp [Nat.cast_smul_eq_nsmul]

theorem deg_h (d : NC ε → Module.End ℂ Z) (j : ℕ) (x : Ch ε Z) (hx : Deg j x) :
    Deg (j + 1) ((∑ i : NC ε, ((lift ε (d i) : Module.End ℂ (Ch ε Z)) * cre i : Module.End ℂ (Ch ε Z))) x) := by
  intro A hA
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i ∈ A
  · have : x (A.erase i) = 0 := hx _ (by
      have := Finset.card_erase_add_one h
      omega)
    simp [cre, h, this]
  · simp [cre, h]

theorem koszul : CAR → Koszul := by
  intro hC n ε Z _ _ a d ha hd hda hnil j x hx hcyc
  set H : Module.End ℂ (Ch ε Z) := ∑ i : NC ε, (lift ε (d i) : Module.End ℂ (Ch ε Z)) * cre i with hH
  have hom : bdA a * H + H * bdA a =
      ∑ i, (lift ε (a i) : Module.End ℂ (Ch ε Z)) * lift ε (d i) + ∑ i, cre i * ann i := by
    refine homotopy_ring (fun i => (lift ε (a i) : Module.End ℂ (Ch ε Z))) (fun i => lift ε (d i)) ann cre
      (fun i j => ann_lift _ _) (fun i j => cre_lift _ _) (fun i j => ?_) (fun i j => (hC n ε Z i j).2.2)
    refine LinearMap.ext fun y => funext fun A => ?_
    have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
    by_cases h : i = j
    · simpa [h] using e
    · simpa [h] using e
  have hsq : ∀ y : Ch ε Z, bdA a (bdA a y) = 0 := by
    intro y
    have e : bdA a * bdA a + bdA a * bdA a = 0 :=
      sq_ring (fun i => (lift ε (a i) : Module.End ℂ (Ch ε Z))) ann (fun i j => ann_lift _ _)
        (fun i j => by
          show lift ε (a i) * lift ε (a j) = lift ε (a j) * lift ε (a i)
          rw [← lift_mul, ← lift_mul, (ha i j).eq]) (fun i j => (hC n ε Z i j).1)
    have e2 := congrArg (fun T : Module.End ℂ (Ch ε Z) => T y) e
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at e2
    rw [← two_smul ℂ] at e2
    exact (smul_eq_zero.mp e2).resolve_left two_ne_zero
  have main : ∀ (m : ℕ) (y : Ch ε Z), (∀ A, y A ∈ filt d m) → Deg (j + 1) y → bdA a y = 0 →
      ∃ t : Ch ε Z, Deg (j + 2) t ∧ bdA a t = y := by
    intro m
    induction m with
    | zero =>
      intro y hy _ _
      refine ⟨0, fun _ _ => rfl, ?_⟩
      rw [map_zero]
      funext A
      simpa [filt, eq_comm] using hy A
    | succ m ih =>
      intro y hy hdeg hc
      have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by
        exact_mod_cast (by omega : m + (j + 1) ≠ 0)
      have hw : ∀ A, (bdA a (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
          (∑ i, a i * d i) (y A) - (m : ℂ) • y A := by
        intro A
        have e := congrArg (fun T : Module.End ℂ (Ch ε Z) => T y A) hom
        simp only [LinearMap.add_apply, Module.End.mul_apply, hc, map_zero, Pi.add_apply, Pi.zero_apply, add_zero,
          number_apply] at e
        have e2 : (A.card : ℂ) • y A = ((j + 1 : ℕ) : ℂ) • y A := by
          by_cases h : A.card = j + 1
          · rw [h]
          · rw [hdeg A h, smul_zero, smul_zero]
        have e3 : ((∑ i, (lift ε (a i) : Module.End ℂ (Ch ε Z)) * lift ε (d i)) y) A =
            (∑ i, a i * d i) (y A) := by
          rw [LinearMap.sum_apply, Finset.sum_apply, LinearMap.sum_apply]
          rfl
        rw [Pi.sub_apply, e, e2, e3, Pi.smul_apply, add_smul]
        abel
      obtain ⟨t, ht, hbt⟩ := ih (bdA a (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
        (fun A => by rw [hw]; exact euler_filt a d hd hda m _ (hy A))
        (fun A hA => by rw [hw, hdeg A hA]; simp)
        (by rw [map_sub, hsq, map_smul, hc]; simp)
      refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), fun A hA => ?_, ?_⟩
      · have := deg_h d (j + 1) y hdeg A hA
        rw [Pi.smul_apply, Pi.sub_apply, ht A hA, this]
        simp
      · rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
  choose f hf using hnil
  refine main (univ.sup fun A => f (x A)) x (fun A => ?_) hx hcyc
  exact filt_mono d (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (mem_filt_of_words d _ _ (hf _))

end GlobalTheory.CompanionTheory.DSICKoszul
