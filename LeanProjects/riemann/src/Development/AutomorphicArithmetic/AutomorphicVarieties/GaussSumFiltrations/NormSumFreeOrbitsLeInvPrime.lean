import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem freeOrbit_prime_dvd_card {p : ℕ} [Fact p.Prime] {α : Type} (σ : α → α) (F : Finset α)
    (hF : ∀ x ∈ F, σ x ∈ F) (hp : ∀ x ∈ F, σ^[p] x = x) (hfree : ∀ x ∈ F, σ x ≠ x) :
    p ∣ F.card := by
  classical
  let f : Function.End F := fun y => ⟨σ y, hF y y.2⟩
  have hf : ∀ (n : ℕ) (y : F), (((f ^ n) y : F) : α) = σ^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Function.iterate_succ_apply', ← ih y]
      rfl
  have h1 : f ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hf]
    exact hp y y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) h1
  have h3 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨y, hy⟩
    exact hfree y y.2 (congrArg Subtype.val hy)
  rw [h3, Fintype.card_coe] at h2
  exact Nat.modEq_zero_iff_dvd.mp h2

theorem norm_prime_Qbar_eq (p : ℕ) [Fact p.Prime] : ‖(p : Qbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.valuation_p p
  rw [← PadicAlgCl.valuation_coe, h]
  simp

theorem norm_sum_free_orbits_le : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  intro p _ ι α σ s Φ hs hp hfree hinv hle
  classical
  have hna := PadicAlgCl.isNonarchimedean p
  have key : ∀ c ∈ s.image Φ,
      ‖ι.symm ((s.filter (fun x => Φ x = c)).card • c)‖ ≤ (p : ℝ)⁻¹ := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    have hd : p ∣ (s.filter (fun x => Φ x = Φ y)).card := by
      apply freeOrbit_prime_dvd_card σ
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hs x hx.1, (hinv x hx.1).trans hx.2⟩
      · intro x hx
        exact hp x (Finset.mem_filter.1 hx).1
      · intro x hx
        exact hfree x (Finset.mem_filter.1 hx).1
    obtain ⟨k, hk⟩ := hd
    rw [map_nsmul, nsmul_eq_mul, norm_mul, hk, Nat.cast_mul, norm_mul, norm_prime_Qbar_eq]
    have h1 : ‖((k : ℕ) : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
    have h2 := hle y hy
    calc (p : ℝ)⁻¹ * ‖((k : ℕ) : Qbar p)‖ * ‖ι.symm (Φ y)‖ ≤ (p : ℝ)⁻¹ * 1 * 1 := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hsum : ∑ x ∈ s, Φ x = ∑ c ∈ s.image Φ, (s.filter (fun x => Φ x = c)).card • c :=
    Finset.sum_comp (fun c => c) Φ
  rw [hsum, map_sum]
  generalize s.image Φ = T at key
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hna _ _).trans (max_le (key a (Finset.mem_insert_self a T))
      (ih fun c hc => key c (Finset.mem_insert_of_mem hc)))

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | exact GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | (intros; apply GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le <;> assumption)
