import Mathlib

namespace GlobalTheory
namespace EvenCubicNorm

open Finset

theorem eq_zero_of_even_cubic {ι X G : Type*} [AddCommGroup X] [AddCommGroup G]
    (b : Module.Basis ι ℤ X) (f : X → G) (hev : ∀ a, f (-a) = f a)
    (hcub : ∀ a a' c, f (a + a' + c) + f a + f a' + f c = f (a + a') + f (a + c) + f (a' + c))
    (h1 : ∀ i, f (b i) = 0) (h2 : ∀ i j, i ≠ j → f (b i + b j) = 0) : ∀ a, f a = 0 := by
  have hext : ∀ g : X →+ G, (∀ i, g (b i) = 0) → ∀ a, g a = 0 := by
    intro g hg a
    have : g.toIntLinearMap = 0 := b.ext (fun i => by simpa using hg i)
    simpa using LinearMap.congr_fun this a
  have h0 : f 0 = 0 := by simpa using hcub 0 0 0
  let B : X → X →+ G := fun c =>
    { toFun := fun a => f (a + c) - f a - f c
      map_zero' := by simp [h0]
      map_add' := by
        intro a a'
        have h := hcub a a' c
        have e : f (a + a' + c) - f (a + a') - f c - (f (a + c) - f a - f c + (f (a' + c) - f a' - f c))
            = (f (a + a' + c) + f a + f a' + f c) - (f (a + a') + f (a + c) + f (a' + c)) := by abel
        rw [← sub_eq_zero, e, h, sub_self] }
  have hBapp : ∀ c a, B c a = f (a + c) - f a - f c := fun _ _ => rfl
  have hdiag : ∀ i, B (b i) (b i) = 0 := by
    intro i
    have h := (B (b i)).map_add (b i) (-(b i))
    rw [add_neg_cancel, map_zero, hBapp (b i) (-(b i)), neg_add_cancel, hev, h0, h1] at h
    simpa using h.symm
  have hA : ∀ j a, B (b j) a = 0 := by
    intro j
    apply hext
    intro i
    by_cases hij : i = j
    · subst hij; exact hdiag i
    · rw [hBapp, h2 i j hij, h1, h1]; simp
  have hAll : ∀ a c, B c a = 0 := by
    intro a c
    have h := hext (B a) (fun j => by rw [hBapp, add_comm (b j) a, ← hA j a, hBapp]; abel) c
    rw [hBapp] at h ⊢
    rw [add_comm c a] at h
    rw [← h]; abel
  let F : X →+ G :=
    { toFun := f
      map_zero' := h0
      map_add' := by
        intro a c
        have h := hAll a c
        rw [hBapp, sub_sub, sub_eq_zero] at h
        exact h }
  intro a
  exact hext F h1 a

section Quadratic

variable {M : Type*} [CommGroup M] {ι : Type*} [Fintype ι]

def prodPow (z : ι → ι → M) (e : ι → ι → ℤ) : M := ∏ i, ∏ j, z i j ^ e i j

theorem prodPow_add (z : ι → ι → M) (e e' : ι → ι → ℤ) :
    prodPow z e * prodPow z e' = prodPow z (fun i j => e i j + e' i j) := by
  simp only [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_single [DecidableEq ι] (z : ι → ι → M) (k l : ι) :
    prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) = z k l := by
  unfold prodPow
  rw [Finset.prod_eq_single k, Finset.prod_eq_single l]
  · simp
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi
    apply Finset.prod_eq_one
    intro j _; simp [hi]
  · simp

end Quadratic

theorem indicator_sum_mul {ι : Type*} [DecidableEq ι] (i j k l : ι) (hkl : k ≠ l) :
    (((if i = k then 1 else 0) + (if i = l then 1 else 0)) * ((if j = k then 1 else 0) + (if j = l then 1 else 0)) : ℤ) =
      (if i = k ∧ j = k then 1 else 0) + (if i = l ∧ j = l then 1 else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) := by
  by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    simp_all

theorem exists_even_cubic_unit_multiple (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (κ₀ : X → (FractionRing R)ˣ)
    (hev : ∀ a, ∃ u : Rˣ, ((κ₀ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (hcub : ∀ a a' b, ∃ u : Rˣ, ((κ₀ (a + a' + b) * κ₀ a * κ₀ a' * κ₀ b : (FractionRing R)ˣ) : FractionRing R) = ((κ₀ (a + a') * κ₀ (a + b) * κ₀ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) :
    ∃ κ : X → (FractionRing R)ˣ, (∀ a, κ (-a) = κ a) ∧
      (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) ∧
      ∀ a, ∃ u : Rˣ, ((κ a : (FractionRing R)ˣ) : FractionRing R) = (κ₀ a : FractionRing R) * algebraMap R (FractionRing R) (u : R) := by
  classical
  set K := FractionRing R
  let φ : Rˣ →* Kˣ := Units.map (algebraMap R K).toMonoidHom
  have hφ : ∀ u : Rˣ, ((φ u : Kˣ) : K) = algebraMap R K (u : R) := fun u => rfl
  let H : Subgroup Kˣ := φ.range
  let ψ : Kˣ → Additive (Kˣ ⧸ H) := fun x => Additive.ofMul (QuotientGroup.mk x)
  have ψmul : ∀ x y, ψ (x * y) = ψ x + ψ y := fun x y => rfl
  have ψφ : ∀ x u, ψ (x * φ u) = ψ x := by
    intro x u
    rw [ψmul]
    have : ψ (φ u) = 0 := by
      show Additive.ofMul (QuotientGroup.mk (φ u) : Kˣ ⧸ H) = 0
      rw [(QuotientGroup.eq_one_iff (φ u)).mpr (MonoidHom.mem_range.mpr ⟨u, rfl⟩)]; rfl
    rw [this, add_zero]
  have ψeq : ∀ x y, ψ x = ψ y → ∃ u : Rˣ, y = x * φ u := by
    intro x y h
    have h' : (QuotientGroup.mk x : Kˣ ⧸ H) = QuotientGroup.mk y := h
    obtain ⟨u, hu⟩ := QuotientGroup.eq.mp h'
    exact ⟨u, by rw [hu]; group⟩
  let b := (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let n : Fin r → X → ℤ := fun i a => b.repr a i
  let z : Fin r → Fin r → Kˣ := fun i j =>
    if i = j then κ₀ (b i) else if i < j then κ₀ (b i + b j) * (κ₀ (b i))⁻¹ * (κ₀ (b j))⁻¹ else 1
  let E : X → Fin r → Fin r → ℤ := fun a i j => n i a * n j a
  let κ : X → Kˣ := fun a => prodPow z (E a)
  have hκ : ∀ a, κ a = prodPow z (E a) := fun _ => rfl
  have κev : ∀ a, κ (-a) = κ a := by
    intro a; simp only [hκ]; congr 1; funext i j; simp [E, n]
  have κcub : ∀ a a' c, κ (a + a' + c) * κ a * κ a' * κ c = κ (a + a') * κ (a + c) * κ (a' + c) := by
    intro a a' c
    simp only [hκ, prodPow_add]
    congr 1; funext i j; simp only [E, n, map_add, Finsupp.add_apply]; ring
  have nb : ∀ i k, n i (b k) = if i = k then 1 else 0 := by
    intro i k; simp [n, Finsupp.single_apply, eq_comm]
  have κb : ∀ k, κ (b k) = κ₀ (b k) := by
    intro k
    have : E (b k) = fun i j => if i = k ∧ j = k then 1 else 0 := by
      funext i j; simp only [E, nb]; split_ifs <;> simp_all
    rw [hκ, this, prodPow_single]; simp [z]
  have κbb : ∀ k l, k < l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    have hne : k ≠ l := ne_of_lt hkl
    have hsplit : prodPow z (E (b k + b l)) =
        prodPow z (fun i j => if i = k ∧ j = k then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = l then 1 else 0) *
        prodPow z (fun i j => if i = k ∧ j = l then 1 else 0) * prodPow z (fun i j => if i = l ∧ j = k then 1 else 0) := by
      simp only [prodPow_add]
      congr 1; funext i j; simp only [E, n, map_add, Finsupp.add_apply]
      have h1 := nb i k; have h2 := nb i l; have h3 := nb j k; have h4 := nb j l
      simp only [n] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      exact indicator_sum_mul i j k l hne
    rw [hκ, hsplit, prodPow_single, prodPow_single, prodPow_single, prodPow_single]
    have hzk : z k k = κ₀ (b k) := by simp only [z]; exact if_pos trivial
    have hzl : z l l = κ₀ (b l) := by simp only [z]; exact if_pos trivial
    have hzkl : z k l = κ₀ (b k + b l) * (κ₀ (b k))⁻¹ * (κ₀ (b l))⁻¹ := by
      simp only [z]; rw [if_neg hne, if_pos hkl]
    have hzlk : z l k = 1 := by simp only [z]; rw [if_neg hne.symm, if_neg (not_lt_of_gt hkl)]
    rw [hzk, hzl, hzkl, hzlk, mul_one, mul_comm (κ₀ (b k) * κ₀ (b l)), mul_assoc, mul_assoc,
      ← mul_assoc (κ₀ (b k))⁻¹, ← mul_inv, inv_mul_cancel, mul_one]
  have κbb' : ∀ k l, k ≠ l → κ (b k + b l) = κ₀ (b k + b l) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact κbb k l h
    · rw [add_comm]; exact κbb l k h

  have κ₀ev : ∀ a, ψ (κ₀ (-a)) = ψ (κ₀ a) := by
    intro a
    obtain ⟨u, hu⟩ := hev a
    have : κ₀ (-a) = κ₀ a * φ u := Units.ext (by rw [Units.val_mul, hφ]; exact hu)
    rw [this, ψφ]
  have κ₀cub : ∀ a a' c, ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) =
      ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)) := by
    intro a a' c
    obtain ⟨u, hu⟩ := hcub a a' c
    have : κ₀ (a + a' + c) * κ₀ a * κ₀ a' * κ₀ c = κ₀ (a + a') * κ₀ (a + c) * κ₀ (a' + c) * φ u :=
      Units.ext (by rw [Units.val_mul _ (φ u), hφ]; exact hu)
    have h := congrArg ψ this
    rw [ψφ] at h
    simpa only [ψmul] using h
  let f : X → Additive (Kˣ ⧸ H) := fun a => ψ (κ (a)) - ψ (κ₀ a)
  have hf : ∀ a, f a = 0 := by
    refine EvenCubicNorm.eq_zero_of_even_cubic b f ?_ ?_ ?_ ?_
    · intro a; simp only [f]; rw [κev, κ₀ev]
    · intro a a' c
      have h1 := κ₀cub a a' c
      have h2 := congrArg ψ (κcub a a' c)
      simp only [ψmul] at h2
      simp only [f]
      have e : ψ (κ (a + a' + c)) - ψ (κ₀ (a + a' + c)) + (ψ (κ a) - ψ (κ₀ a)) + (ψ (κ a') - ψ (κ₀ a')) +
            (ψ (κ c) - ψ (κ₀ c)) - (ψ (κ (a + a')) - ψ (κ₀ (a + a')) + (ψ (κ (a + c)) - ψ (κ₀ (a + c))) +
            (ψ (κ (a' + c)) - ψ (κ₀ (a' + c)))) =
          (ψ (κ (a + a' + c)) + ψ (κ a) + ψ (κ a') + ψ (κ c) - (ψ (κ (a + a')) + ψ (κ (a + c)) + ψ (κ (a' + c)))) -
          (ψ (κ₀ (a + a' + c)) + ψ (κ₀ a) + ψ (κ₀ a') + ψ (κ₀ c) -
            (ψ (κ₀ (a + a')) + ψ (κ₀ (a + c)) + ψ (κ₀ (a' + c)))) := by abel
      rw [← sub_eq_zero, e, h1, h2, sub_self, sub_self, sub_self]
    · intro i; simp only [f]; rw [κb, sub_self]
    · intro i j hij; simp only [f]; rw [κbb' i j hij, sub_self]
  refine ⟨κ, κev, κcub, fun a => ?_⟩
  have h := hf a
  simp only [f, sub_eq_zero] at h
  obtain ⟨u, hu⟩ := ψeq _ _ h.symm
  exact ⟨u, by rw [hu, Units.val_mul, hφ]⟩

end EvenCubicNorm
end GlobalTheory
