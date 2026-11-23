import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPeelingMinorMemIdeal

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem la_ideal {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x : A} (hx : x ∈ Ideal.span (rgen k r z' E)) : La x = 0 := by
  have key : ∀ y ∈ Ideal.span (rgen k r z' E), ∀ a : A, La (a * y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, hpq, rfl⟩ := hy
      intro a
      rw [mul_sub, map_sub, hR a p q hpq, ← Algebra.commutes, ← Algebra.smul_def, map_smul, sub_self]
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add, hx, hy, add_zero]
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b)
  simpa using key x hx 1

theorem la_congr {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x y : A} (hx : x - y ∈ Ideal.span (rgen k r z' E)) : La x = La y := by
  have := la_ideal hR hx
  rwa [map_sub, sub_eq_zero] at this

theorem sum_single {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} (P : (Fin m → Fin N) → Prop)
    [DecidablePred P] (X : Fin m → Fin N → ℂ) (S : Set (Fin N)) (hX : ∀ a p, p ∉ S → X a p = 0)
    (e : Fin m → Fin N) (he : P e) (huniq : ∀ c, P c → (∀ l, c l ∈ S) → c = e) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      (Matrix.of fun a l => X a (e l)).det • F e := by
  rw [Finset.sum_eq_single e]
  · rw [if_pos he]
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, c l ∈ S
      · exact absurd (huniq c hP hS) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hX a _ hl]), zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ e) h

theorem uniq_mono {α : Type} [LinearOrder α] {m : ℕ} (e c : Fin m → α) (he : StrictMono e) (hc : StrictMono c)
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have hcard : (Finset.image e Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ he.injective]; simp
  have hS' : ∀ l, c l ∈ Finset.image e Finset.univ := by
    intro l; obtain ⟨x, hx⟩ := hS l; rw [← hx]; exact Finset.mem_image_of_mem e (Finset.mem_univ x)
  rw [Finset.orderEmbOfFin_unique hcard hS' hc]
  exact (Finset.orderEmbOfFin_unique hcard (fun l => Finset.mem_image_of_mem e (Finset.mem_univ l)) he).symm

theorem uniq_key {N m : ℕ} (key : Fin N → ℕ) (hkey : Function.Injective key) (e c : Fin m → Fin N)
    (he : StrictMono (fun l => key (e l))) (hc : StrictMono (fun l => key (c l)))
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have h := uniq_mono (fun l => key (e l)) (fun l => key (c l)) he hc (by
    intro l; obtain ⟨x, hx⟩ := hS l; exact ⟨x, by simp only [hx]⟩)
  funext l; exact hkey (congrFun h l)

theorem AAx_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (u : ℂ) :
    AAx k r E xi m1 h1 u = AAx k r E xi m2 h2 u := by subst h; rfl

theorem AAv_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (ell : ℂ) :
    AAv k r E y m1 h1 ell = AAv k r E y m2 h2 ell := by subst h; rfl

theorem sgnW_sq (m : ℕ) : sgnW m * sgnW m = 1 := by
  unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem scal_E (dh t σ ε : ℂ) (s' : ℕ) (hdh : dh ≠ 0) (ht : t ≠ 0) (hσ : σ * σ = 1) (hε : ε * ε = 1) :
    (dh * t ^ (s' + 1) * (ε * σ))⁻¹ * (dh * t ^ s' * σ) = ε * t⁻¹ * (dh⁻¹ * dh) := by
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, zero_mul] at hσ; exact zero_ne_one hσ
  have hε0 : ε ≠ 0 := by intro h0; rw [h0, zero_mul] at hε; exact zero_ne_one hε
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
  rw [mul_inv, mul_inv, mul_inv, hεi, inv_mul_cancel₀ hdh, pow_succ]
  field_simp

theorem AAx_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → i0 ≤ p.val → xi a p = 0)
    (hh : ∀ a b : Fin i0, xi (Fin.castLE hi0 a) (xR k r i0 hi0 b) = h a b) :
    AAx k r E xi i0 hi0 u = h.det • qminor E (xR k r i0 hi0) (xR k r i0 hi0) u := by
  unfold AAx
  rw [sum_single (fun c => StrictMono c) (fun a p => xi (Fin.castLE hi0 a) p) (Set.range (xR k r i0 hi0))
    ?_ (xR k r i0 hi0) ?_ ?_]
  · congr 2
    ext a l
    simp only [Matrix.of_apply]
    exact hh a l
  · intro a p hp
    apply hz _ _ (by simp)
    by_contra hlt; push Not at hlt; apply hp; exact ⟨⟨p.val, hlt⟩, by ext; simp [xR, eI]⟩
  · intro a b hab; simp only [xR, eI]; exact hab
  · intro c hc hS
    exact uniq_mono _ _ (fun a b hab => by simp only [xR, eI]; exact hab) hc hS

end Formalism.FourierDecayAlt.P.SignAntidiagonal
