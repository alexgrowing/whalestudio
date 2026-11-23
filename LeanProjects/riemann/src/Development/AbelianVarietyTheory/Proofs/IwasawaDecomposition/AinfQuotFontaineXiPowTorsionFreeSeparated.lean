import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem quot_pow_torsionFree_sep {A O : Type*} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O]
    (θ : A →+* O) (ξ p : A) (hξ : ξ ≠ 0) (hker : ∀ a, θ a = 0 ↔ ξ ∣ a) (hp : θ p ≠ 0)
    (hsep : ∀ x : O, (∀ k : ℕ, θ p ^ k ∣ x) → x = 0) (n : ℕ) :
    (∀ a : A, ξ ^ n ∣ p * a → ξ ^ n ∣ a) ∧
      ∀ a : A, (∀ k : ℕ, ∃ b : A, ξ ^ n ∣ a - p ^ k * b) → ξ ^ n ∣ a := by
  have h0 : ∀ (m : ℕ) (x : A), ξ ^ (m + 1) ∣ x → θ x = 0 := fun m x hx =>
    (hker x).2 ((dvd_pow_self ξ m.succ_ne_zero).trans hx)
  have hθξ : θ ξ = 0 := (hker ξ).2 dvd_rfl
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have h1 := h0 n _ ha
      rw [map_mul] at h1
      obtain ⟨a', rfl⟩ := (hker a).1 ((mul_eq_zero.1 h1).resolve_left hp)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hξ] at ha
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      exact ih.1 a' ha
    · have h1 : θ a = 0 := hsep _ fun k => by
        obtain ⟨b, hb⟩ := ha k
        have h2 := h0 n _ hb
        rw [map_sub, map_mul, map_pow, sub_eq_zero] at h2
        exact ⟨θ b, h2⟩
      obtain ⟨a', rfl⟩ := (hker a).1 h1
      rw [pow_succ', mul_dvd_mul_iff_left hξ]
      refine ih.2 a' fun k => ?_
      obtain ⟨b, hb⟩ := ha k
      have h2 := h0 n _ hb
      rw [map_sub, h1, map_mul, map_pow, zero_sub, neg_eq_zero] at h2
      obtain ⟨b', rfl⟩ := (hker b).1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero k hp))
      refine ⟨b', ?_⟩
      rwa [pow_succ', mul_left_comm, ← mul_sub, mul_dvd_mul_iff_left hξ] at hb

theorem ainf_quot_xi_pow_torsionFree_sep : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ ∀ a : Per.Ainf l, (∀ k : ℕ, ∃ b : Per.Ainf l, xi e ^ n ∣ a - ((l : ℕ) : Per.Ainf l) ^ k * b) → xi e ^ n ∣ a := by
  intro l _ e he n
  obtain ⟨-, hdom, -, hk⟩ := theta_ker_facts l
  obtain ⟨h1, h2⟩ := hk e he
  refine quot_pow_torsionFree_sep (Per.θ l) (xi e) _ h2 (fun a => ?_) ?_ (fun x hx => ?_) n
  · rw [← RingHom.mem_ker, h1, Ideal.mem_span_singleton]
  · rw [map_natCast]
    exact fun h => GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  · rw [map_natCast] at hx
    refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.OC l)}) inferInstance x fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx k

end GlobalTheory.MemLoc
