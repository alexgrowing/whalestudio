import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.DvdPowQSub

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]

theorem norm_tau_unit (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : ‖τ (a : K)‖ = 1 := by
  obtain ⟨b, hb⟩ := exists_inv_mod hP ha
  have h1 := norm_tau_dvd τ (a := a * b - 1) (k := 1) (by rw [pow_one]; exact hb)
  rw [pow_one] at h1
  have hab : τ ((a * b - 1 : 𝓞 K) : K) = τ (a : K) * τ (b : K) - 1 := by
    rw [tau_sub]
    simp
  rw [hab] at h1
  have hlt : (p : ℝ)⁻¹ < 1 := pinv_lt_one
  refine le_antisymm (norm_tau_le τ a) ?_
  refine not_lt.1 fun hlt' => ?_
  have hprod : ‖τ (a : K) * τ (b : K)‖ < 1 := by
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt' (norm_tau_le τ b)
  have hmax : ‖(1 : ℂ_[p])‖ ≤ max ‖τ (a : K) * τ (b : K)‖ ‖τ (a : K) * τ (b : K) - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max (τ (a : K) * τ (b : K)) (-(τ (a : K) * τ (b : K) - 1))
    rwa [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
  rw [norm_one] at hmax
  exact absurd hmax (not_le.2 (max_lt hprod (h1.trans_lt hlt)))

theorem dvd_of_close (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a b : 𝓞 K}
    (h : ‖τ (a : K) - τ (b : K)‖ < 1) : (p : 𝓞 K) ∣ a - b := by
  by_contra hn
  have h1 := norm_tau_unit τ hP hn
  rw [tau_sub] at h1
  linarith

variable (hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b)
include hq

theorem teich_ne_zero (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : teich τ a ≠ 0 := by
  intro h0
  have hc := teich_close τ hq a
  rw [h0, zero_sub, norm_neg, norm_tau_unit τ hP ha] at hc
  linarith [pinv_lt_one (p := p)]

theorem teich_root (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a : 𝓞 K}
    (ha : ¬ (p : 𝓞 K) ∣ a) : teich τ a ^ (p ^ 2 - 1) = 1 := by
  have hpow := teich_pow τ hq a
  have hne := teich_ne_zero hq τ hP ha
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  have he : teich τ a ^ (p ^ 2 - 1) * teich τ a = 1 * teich τ a := by
    rw [← pow_succ, Nat.sub_add_cancel h1, hpow, one_mul]
  exact mul_right_cancel₀ hne he

theorem teich_inj (τ : K →+* ℂ_[p]) (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {a b : 𝓞 K}
    (h : teich τ a = teich τ b) : (p : 𝓞 K) ∣ a - b := by
  apply dvd_of_close τ hP
  have ha := teich_close τ hq a
  have hb := teich_close τ hq b
  have e : τ (a : K) - τ (b : K) = (teich τ b - τ (b : K)) - (teich τ a - τ (a : K)) := by
    rw [h]; ring
  rw [e]
  calc _ ≤ max ‖teich τ b - τ (b : K)‖ ‖teich τ a - τ (a : K)‖ := by
        rw [sub_eq_add_neg _ (teich τ a - τ (a : K)), ← norm_neg (teich τ a - τ (a : K))]
        exact IsUltrametricDist.norm_add_le_max _ _
    _ ≤ (p : ℝ)⁻¹ := max_le hb ha
    _ < 1 := pinv_lt_one

theorem teich_surj (hK : Module.finrank ℚ K = 2) (τ : K →+* ℂ_[p])
    (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) {ζ : ℂ_[p]} (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    ∃ a : 𝓞 K, teich τ a = ζ := by
  classical
  have : (Ideal.span {(p : 𝓞 K)}).IsMaximal := isMaximal_span_p hP
  letI : Field (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := finite_quot hK
  letI : Fintype (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) := Fintype.ofFinite _
  set g : 𝓞 K ⧸ Ideal.span {(p : 𝓞 K)} → 𝓞 K :=
    Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(p : 𝓞 K)})) with hgdef
  have hg : ∀ x, Ideal.Quotient.mk _ (g x) = x := Function.surjInv_eq _
  have hn : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hp.out.one_lt)
  have hnd : ∀ u : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})ˣ, ¬ (p : 𝓞 K) ∣ g u := fun u hd =>
    u.ne_zero (by rw [← hg u]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hd))
  let f : (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})ˣ → ℂ_[p] := fun u => teich τ (g u)
  have hf : Function.Injective f := fun u v huv => Units.ext (by
    rw [← hg u, ← hg v]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (teich_inj hq τ hP huv)))
  set T := (Polynomial.nthRoots (p ^ 2 - 1) (1 : ℂ_[p])).toFinset with hT
  have hsub : Finset.univ.image f ⊆ T := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact teich_root hq τ hP (hnd u)
  have hcardQ : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_quot hK
  have hcardU : Fintype.card (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)})ˣ = p ^ 2 - 1 := by
    rw [Fintype.card_units, hcardQ]
  have hcardT : T.card ≤ p ^ 2 - 1 :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  have heq : Finset.univ.image f = T := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hcardU]
    exact hcardT)
  have hζT : ζ ∈ T := by
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hζ
  rw [← heq] at hζT
  obtain ⟨u, -, hu⟩ := Finset.mem_image.1 hζT
  exact ⟨g u, hu⟩

end PI.OkpW
