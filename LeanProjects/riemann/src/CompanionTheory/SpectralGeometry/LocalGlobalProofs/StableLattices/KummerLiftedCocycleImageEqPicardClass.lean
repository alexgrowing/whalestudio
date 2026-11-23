import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSVerma

open CompanionTheory.D.DSIC Formalism.REAL

variable {n : ℕ} {ε : Fin n → Bool}

theorem sum_nc {R : Type} [AddCommMonoid R] (d b : Fin n) (g : Fin n → Fin n → R) :
    (∑ j : NC ε, if d = j.1.1 ∧ b = j.1.2 then g j.1.1 j.1.2 else 0) =
      if ε d = true ∧ ε b = false then g d b else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(d, b), h⟩ : NC ε)]
    · simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hj (Subtype.ext (Prod.ext h1.symm h2.symm))
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [h1, h2]; exact j.2)

section Abstract

variable {R : Type} [Ring R] (Y : NC ε → R) (u v : Fin n → Fin n → R)

theorem inner_sum
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (i : NC ε) (c d e f : Fin n) :
    (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) =
      u i.1.1 c * (if ε d = true then u d e else 0) * v f i.1.2 -
        v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) := by
  have h1 : ∀ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2) =
      (if d = j.1.1 ∧ i.1.2 = j.1.2 then u i.1.1 c * u j.1.1 e * v f j.1.2 else 0) -
        (if i.1.1 = j.1.1 ∧ c = j.1.2 then v d i.1.2 * u j.1.1 e * v f j.1.2 else 0) := by
    intro j
    have : (u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2) =
        u i.1.1 c * (v d i.1.2 * Y j - Y j * v d i.1.2) + (u i.1.1 c * Y j - Y j * u i.1.1 c) * v d i.1.2 := by
      noncomm_ring
    rw [this, huY, hvY]
    split_ifs <;> noncomm_ring
  simp only [h1, Finset.sum_sub_distrib]
  rw [sum_nc d i.1.2 (fun a b => u i.1.1 c * u a e * v f b),
    sum_nc i.1.1 c (fun a b => v d i.1.2 * u a e * v f b)]
  simp only [i.2.1, i.2.2, and_true, true_and]
  split_ifs <;> simp

theorem glRel_abstract (hYY : ∀ i j, Commute (Y i) (Y j))
    (huu : ∀ a b c d, Commute (u a b) (u c d)) (huv : ∀ a b c d, Commute (u a b) (v c d))
    (hvv : ∀ a b c d, Commute (v a b) (v c d))
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (hs : ∀ d e, (if ε d = true then u d e else 0) + (if ε e = false then v d e else 0) =
      if d = e then 1 else 0) (c d e f : Fin n) :
    (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) -
      (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) =
      (if d = e then ∑ i : NC ε, Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then ∑ i : NC ε, Y i * (u i.1.1 e * v d i.1.2) else 0) := by
  have hprod : ∀ p q : NC ε → R, (∑ i, Y i * p i) * (∑ j, Y j * q j) =
      ∑ i, ∑ j, Y i * Y j * (p i * q j) + ∑ i, Y i * ∑ j, (p i * Y j - Y j * p i) * q j := by
    intro p q
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    noncomm_ring
  rw [hprod, hprod]
  have hsym : (∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 c * v d i.1.2 * (u j.1.1 e * v f j.1.2))) =
      ∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 e * v f i.1.2 * (u j.1.1 c * v d j.1.2)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hYY j i).eq, (((huu _ _ _ _).mul_right (huv _ _ _ _)).mul_left
      ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _))).eq]
  rw [hsym, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  have key : ∀ i : NC ε,
      Y i * (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) -
      Y i * (∑ j : NC ε, ((u i.1.1 e * v f i.1.2) * Y j - Y j * (u i.1.1 e * v f i.1.2)) * (u j.1.1 c * v d j.1.2)) =
      (if d = e then Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then Y i * (u i.1.1 e * v d i.1.2) else 0) := by
    intro i
    rw [inner_sum Y u v huY hvY, inner_sum Y u v huY hvY]
    have e1 : ∀ c d e f : Fin n, v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) =
        u i.1.1 e * (if ε c = false then v f c else 0) * v d i.1.2 := by
      intro c d e f
      split_ifs
      · rw [mul_assoc]
        exact ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _)).eq
      · simp
    rw [e1, e1]
    have h1 := hs d e
    have h2 := hs f c
    generalize (if ε d = true then u d e else 0) = A at *
    generalize (if ε e = false then v d e else 0) = B at *
    generalize (if ε f = true then u f c else 0) = C at *
    generalize (if ε c = false then v f c else 0) = D at *
    calc _ = Y i * (u i.1.1 c * (A + B) * v f i.1.2) - Y i * (u i.1.1 e * (C + D) * v d i.1.2) := by noncomm_ring
      _ = _ := by rw [h1, h2]; split_ifs <;> simp
  simp only [key, Finset.sum_sub_distrib]
  split_ifs <;> simp

end Abstract

open MvPolynomial

def dd (ε : Fin n → Bool) (a b : Fin n) : Module.End ℂ (MvPolynomial (NC ε) ℂ) :=
  if h : ε a = true ∧ ε b = false then (pderiv (⟨(a, b), h⟩ : NC ε)).toLinearMap else 0

def yy (i : NC ε) : Module.End ℂ (MvPolynomial (NC ε) ℂ) := LinearMap.mulLeft ℂ (X i)

theorem pderiv_comm' {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem dd_comm (a b c d : Fin n) : Commute (dd ε a b) (dd ε c d) := by
  unfold dd
  split_ifs
  · refine LinearMap.ext fun f => ?_
    exact pderiv_comm' _ _ f
  all_goals simp

theorem dd_yy (a c : Fin n) (j : NC ε) :
    dd ε a c * yy j - yy j * dd ε a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0 := by
  classical
  unfold dd yy
  split_ifs with h1 h2 h2
  · refine LinearMap.ext fun f => ?_
    have : j = ⟨(a, c), h1⟩ := Subtype.ext (Prod.ext h2.1.symm h2.2.symm)
    subst this
    simp
  · refine LinearMap.ext fun f => ?_
    have : j ≠ ⟨(a, c), h1⟩ := by
      rintro rfl
      exact h2 ⟨rfl, rfl⟩
    simp [pderiv_X_of_ne this]
  · exact absurd (by rw [h2.1, h2.2]; exact j.2) h1
  · simp

theorem verma : CompanionTheory.D.DSIC.Verma := by
  intro n ε
  let u : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) - dd ε a c
  let v : Fin n → Fin n → Module.End ℂ (MvPolynomial (NC ε) ℂ) := fun a c => (if a = c then 1 else 0) + dd ε a c
  have hδ : ∀ (a c : Fin n) (T : Module.End ℂ (MvPolynomial (NC ε) ℂ)),
      Commute (if a = c then 1 else 0) T := by
    intro a c T
    split_ifs <;> simp
  refine ⟨fun c d => ∑ i : NC ε, yy i * (u i.1.1 c * v d i.1.2), ?_, ?_, ?_⟩
  · intro c d e f
    refine glRel_abstract yy u v ?_ ?_ ?_ ?_ ?_ ?_ ?_ c d e f
    · intro i j
      refine LinearMap.ext fun f => ?_
      simp [yy, mul_left_comm]
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.sub_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).sub_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a b c d
      exact (hδ _ _ _).add_left ((hδ _ _ _).symm.add_right (dd_comm _ _ _ _))
    · intro a c j
      rw [← dd_yy]
      simp only [u, sub_mul, mul_sub, (hδ a c (yy j)).eq]
      abel
    · intro a c j
      rw [← dd_yy]
      simp only [v, add_mul, mul_add, (hδ a c (yy j)).eq]
      abel
    · intro d e
      have h0 : ¬(ε d = true ∧ ε e = false) → dd ε d e = 0 := fun h => dif_neg h
      simp only [u, v]
      generalize dd ε d e = T at *
      by_cases hde : d = e
      · subst hde
        cases h : ε d <;> simp_all
      · cases h : ε d <;> cases h' : ε e <;> simp_all
  · intro i f
    have hu : ∀ j : NC ε, u j.1.1 i.1.1 = if j.1.1 = i.1.1 then 1 else 0 := by
      intro j
      simp [u, dd, i.2.1]
    have hv : ∀ j : NC ε, v i.1.2 j.1.2 = if i.1.2 = j.1.2 then 1 else 0 := by
      intro j
      simp [v, dd, i.2.2]
    simp only [hu, hv]
    rw [Finset.sum_eq_single i]
    · simp [yy]
    · intro j _ hj
      split_ifs with h1 h2
      · exact absurd (Subtype.ext (Prod.ext h1 h2.symm)) hj
      all_goals simp
    · simp
  · intro a b f
    simp [yy, LinearMap.sum_apply, map_sum]

end GlobalTheory.CompanionTheory.DSVerma
