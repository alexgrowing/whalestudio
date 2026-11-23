import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Decay

theorem pow_add_mul_range {M R : Type} [AddCommGroup M] [CommRing R] (f : M →+ R)
    (hm : ∀ x y : M, ∃ z, f z = f x * f y) (x y : M) (c n : ℕ) :
    ∃ p g : M, f p = f x ^ (n + 1) ∧ (f x + c * f y) ^ (n + 1) = f x ^ (n + 1) + c * f g := by
  induction n with
  | zero => exact ⟨x, y, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨p, g, hp, hg⟩ := ih
    obtain ⟨p', hp'⟩ := hm p x
    obtain ⟨z1, h1⟩ := hm p y
    obtain ⟨z2, h2⟩ := hm g x
    obtain ⟨z3, h3⟩ := hm g y
    refine ⟨p', z1 + z2 + c • z3, by rw [hp', hp]; ring, ?_⟩
    rw [pow_succ, hg, map_add, map_add, map_nsmul, h1, h2, h3, hp, nsmul_eq_mul]
    ring

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) :=
  AddMonoidHom.mk' (ofW t K e) fun x y => by
    funext τ
    ext i n
    simp only [Pi.add_apply, map_add, coeff_ofW, add_div]

theorem ofWHom_apply (w : ℕ × ℕ → Wq l a) : ofWHom t K e w = ofW t K e w := rfl

theorem eq_zero_of_coeff [CharZero K]
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c))
    (w : ℕ × ℕ → Wq l a) (i n : ℕ) (h : coeff n (coeff i (ofW t K e w 0)) = 0) : w (i, n) = 0 := by
  rw [coeff_ofW, div_eq_zero_iff] at h
  have h2 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  apply hinj 0
  simpa using h.resolve_right h2

theorem ofWHom_injective [CharZero K]
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) :
    Function.Injective (ofWHom t K e) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  funext ⟨i, n⟩
  apply eq_zero_of_coeff t K e hinj
  rw [← ofWHom_apply, hw]
  simp

theorem box_cofinite (M : ℕ) : ∀ᶠ p : ℕ × ℕ in cofinite, M < p.1 ∨ M < p.2 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_Iic M).prod (Set.finite_Iic M)).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq, not_or, not_lt] at h
  exact h

end GlobalTheory.CrysPrism.Decay

namespace GlobalTheory.CrysPrism
open Decay

theorem frob_keeps_decay (l : ℕ) [hl : Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c))
    (hmul : ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e)
    (hQ : ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂)
    (hsupp : ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) →
      ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n →
        coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0)
    (w : ℕ × ℕ → Wq l a) (hw : LTo0 l w) (v b : ℕ × ℕ → Wq l a)
    (hv : frob2 φ₂ (ofW t K e w) = ofW t K e v)
    (hb : frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b) :
    LTo0 l v ∧ LTo0 l b := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps (natCast_ne_zero_ps hl0)
  have hI := ofWHom_injective t K e hinj
  have key : ∀ r : ℕ, ∀ᶠ p in cofinite, (l : Wq l a) ^ r ∣ v p ∧ (l : Wq l a) ^ r ∣ b p := by
    intro r
    have hS := hw (r + 1)
    rw [Filter.eventually_cofinite] at hS
    obtain ⟨⟨N1, N2⟩, hN⟩ := hS.bddAbove
    let w1 : ℕ × ℕ → Wq l a := fun p => if (l : Wq l a) ^ (r + 1) ∣ w p then 0 else w p
    have hex : ∀ p, ∃ c, w p = w1 p + (l ^ (r + 1) : ℕ) • c := by
      intro p
      by_cases h : (l : Wq l a) ^ (r + 1) ∣ w p
      · obtain ⟨c, hc⟩ := id h
        refine ⟨c, ?_⟩
        simp only [w1, if_pos h]
        simp [hc]
      · exact ⟨0, by simp only [w1, if_neg h]; simp⟩
    choose w2 hw2 using hex
    have hw12 : w = w1 + (l ^ (r + 1) : ℕ) • w2 := funext hw2
    have hw1 : ∀ i n, max N1 N2 < i ∨ max N1 N2 < n → w1 (i, n) = 0 := by
      intro i n h
      by_cases h' : (l : Wq l a) ^ (r + 1) ∣ w (i, n)
      · simp only [w1, if_pos h']
      · have h3 : (i, n) ≤ (N1, N2) := hN h'
        obtain ⟨h4, h5⟩ := h3
        simp only at h4 h5
        omega
    obtain ⟨M, hM⟩ := hsupp _ w1 hw1
    obtain ⟨-, ⟨v1, hv1⟩, _, ⟨b1, rfl⟩, hb1⟩ := hQ _ ⟨w1, rfl⟩
    obtain ⟨-, ⟨v2, hv2⟩, -⟩ := hQ _ ⟨w2, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.out.ne_zero
    obtain ⟨-, g, -, hg⟩ := pow_add_mul_range (ofWHom t K e)
      (fun x y => hmul _ ⟨x, rfl⟩ _ ⟨y, rfl⟩) w1 w2 (l ^ (r + 1)) k
    rw [← hk] at hg
    have hF : ofW t K e w = ofW t K e w1 + ((l ^ (r + 1) : ℕ) : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e w2 := by
      rw [← ofWHom_apply, hw12, map_add, map_nsmul, nsmul_eq_mul]; rfl
    have hφ : frob2 φ₂ (ofW t K e w) =
        ofW t K e v1 + ((l ^ (r + 1) : ℕ) : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e v2 := by
      rw [hF, map_add, map_mul, map_natCast, hv1, hv2]
    have e1 : v = v1 + (l ^ (r + 1) : ℕ) • v2 := by
      apply hI
      rw [map_add, map_nsmul, nsmul_eq_mul, ofWHom_apply, ← hv, hφ]; rfl
    have e2 : b = b1 + (l ^ r : ℕ) • (v2 - g) := by
      apply hI
      rw [map_add, map_nsmul, map_sub, nsmul_eq_mul, ← sub_eq_zero]
      apply tf_pi hl2
      simp only [ofWHom_apply] at hg ⊢
      rw [← hF] at hg
      rw [← hv1] at hb1
      push_cast at hg hφ ⊢
      linear_combination hφ - hb - hg + hb1
    filter_upwards [box_cofinite M] with ⟨i, n⟩ hp
    obtain ⟨m1, m2⟩ := hM 0 i n hp
    have z1 : v1 (i, n) = 0 := eq_zero_of_coeff t K e hinj v1 i n (by rw [hv1]; exact m1)
    have z2 : b1 (i, n) = 0 := by
      apply eq_zero_of_coeff t K e hinj
      rw [hb1, ← nsmul_eq_mul, Pi.add_apply, map_add, map_add, m2, zero_add, Pi.smul_apply, map_nsmul, map_nsmul,
        nsmul_eq_mul] at m1
      exact (mul_eq_zero.1 m1).resolve_left hl0
    constructor
    · rw [e1]
      simp only [Pi.add_apply, Pi.smul_apply, z1, zero_add, nsmul_eq_mul, Nat.cast_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (Nat.le_succ r)) _
    · rw [e2]
      simp only [Pi.add_apply, Pi.smul_apply, z2, zero_add, nsmul_eq_mul, Nat.cast_pow]
      exact Dvd.intro _ rfl
  exact ⟨fun r => (key r).mono fun _ h => h.1, fun r => (key r).mono fun _ h => h.2⟩

end GlobalTheory.CrysPrism
