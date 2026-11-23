import Mathlib

namespace GlobalTheory.CompanionTheory.ColimLift

variable {G : ℕ → Type} [∀ n, CommRing (G n)] (f : ∀ n, G n →+* G (n + 1))
  {L : Type} [CommRing L] (ι : ∀ n, G n →+* L)
  (t : ∀ n k, G n → G (n + k))

theorem apply_iter {T : Type} (y : ∀ n, G n → T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n k : ℕ) (x : G n) :
    y (n + k) (t n k x) = y n x := by
  induction k with
  | zero => exact congrArg (y n) (t0 n x)
  | succ k ih =>
    have h : y (n + (k + 1)) (t n (k + 1) x) = y (n + k + 1) (f (n + k) (t n k x)) :=
      congrArg (y (n + k + 1)) (tS n k x)
    rw [h, hy, ih]

theorem eq_of_same_stage {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n : ℕ) (a b : G n) (h : ι n a = ι n b) :
    y n a = y n b := by
  obtain ⟨k, hk⟩ := ker n (a - b) (by rw [map_sub, h, sub_self])
  have h1 := apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k (a - b)
  simp only [hk, map_zero, map_sub] at h1
  exact sub_eq_zero.mp h1.symm

theorem eq_of_iota_eq {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n m : ℕ) (a : G n) (b : G m)
    (h : ι n a = ι m b) : y n a = y m b := by
  have up : ∀ (n m : ℕ), n ≤ m → ∀ a : G n, ∃ a' : G m, ι m a' = ι n a ∧ y m a' = y n a := by
    intro n m hnm a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨t n k a, apply_iter f t (fun n => (ι n : G n → L)) t0 tS hι n k a,
      apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k a⟩
  obtain ⟨a', ha, hya⟩ := up n (max n m) (le_max_left _ _) a
  obtain ⟨b', hb, hyb⟩ := up m (max n m) (le_max_right _ _) b
  rw [← hya, ← hyb]
  exact eq_of_same_stage f ι t y t0 tS ker hy _ a' b' (by rw [ha, hb, h])

theorem exists_lift_of_surj_ker
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (surj : ∀ (m : ℕ) (v : Fin m → L), ∃ n, ∃ w : Fin m → G n, ∀ i, ι n (w i) = v i)
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    {T : Type} [CommRing T] (y : ∀ n, G n →+* T) (hy : ∀ n x, y (n + 1) (f n x) = y n x) :
    ∃ z : L →+* T, ∀ n x, z (ι n x) = y n x := by
  classical
  have key := eq_of_iota_eq f ι t y hι t0 tS ker hy
  have rep : ∀ l : L, ∃ n, ∃ a : G n, ι n a = l := fun l => by
    obtain ⟨n, w, hw⟩ := surj 1 (fun _ => l)
    exact ⟨n, w 0, hw 0⟩
  choose r s hs using rep
  let z : L → T := fun l => y (r l) (s l)
  have hz : ∀ n x, z (ι n x) = y n x := fun n x => key _ _ _ _ (hs _)
  have two : ∀ l₁ l₂ : L, ∃ n, ∃ a b : G n, ι n a = l₁ ∧ ι n b = l₂ := fun l₁ l₂ => by
    obtain ⟨n, w, hw⟩ := surj 2 ![l₁, l₂]
    exact ⟨n, w 0, w 1, hw 0, hw 1⟩
  refine ⟨{ toFun := z, map_one' := ?_, map_zero' := ?_, map_mul' := ?_, map_add' := ?_ }, hz⟩
  · have := hz 0 1
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_mul, hz, hz, hz, map_mul]
  · have := hz 0 0
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_add, hz, hz, hz, map_add]

end GlobalTheory.CompanionTheory.ColimLift
