import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam

noncomputable section

namespace GlobalTheory.CompanionTheory.FinHeis.Irred

open GlobalTheory.CompanionTheory.FinHeis

variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)

theorem c_ne (x y : X) : S.c x y ≠ 0 := by
  intro h
  have := S.c_norm x y
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem c_swap (x y : X) : S.c x y * S.c y x = 1 := by
  have h := S.c_self (x + y)
  rw [S.c_add_left, S.c_add_right, S.c_add_right, S.c_self, S.c_self] at h
  linear_combination h

theorem rho_comm (x y : X) (v : M) :
    S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by
  rw [S.rho_rho, S.rho_rho, smul_smul, add_comm y x]
  congr 1
  linear_combination (-S.c x y) * c_swap S x y

theorem eigen {al : X → ℂ} {Γ : AddSubgroup X} {φ : M} (hs : IsSemi S al Γ) (hl : Law S al Γ φ)
    {γ : X} (hγ : γ ∈ Γ) (x : X) :
    al γ • S.rho γ (S.rho x φ) = S.c γ x ^ 2 • S.rho x φ := by
  have ha : al γ ≠ 0 := by
    rcases hs.1 γ hγ with h | h <;> rw [h] <;> norm_num
  rw [rho_comm, hl γ hγ, map_smul, smul_smul, smul_smul]
  congr 1
  field_simp

theorem mem_of_sum {al : X → ℂ} {Γ : AddSubgroup X} {φ : M} (hd : SelfDual S Γ)
    (hs : IsSemi S al Γ) (hl : Law S al Γ φ) (N : Submodule ℂ M)
    (hN : ∀ x, ∀ v ∈ N, S.rho x v ∈ N) (s : Finset X) :
    ∀ a : X → ℂ, (∑ x ∈ s, a x • S.rho x φ) ∈ N → (∑ x ∈ s, a x • S.rho x φ) ≠ 0 → φ ∈ N := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro a hm hne
    have key : ∀ γ ∈ Γ, ∀ x₀ ∈ s,
        al γ • S.rho γ (∑ x ∈ s, a x • S.rho x φ) - S.c γ x₀ ^ 2 • (∑ x ∈ s, a x • S.rho x φ)
          = ∑ x ∈ s.erase x₀, (a x * (S.c γ x ^ 2 - S.c γ x₀ ^ 2)) • S.rho x φ := by
      intro γ hγ x₀ _
      rw [Finset.sum_erase _ (by simp), map_sum, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, smul_comm (al γ), eigen S hs hl hγ, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    by_cases h : ∃ γ ∈ Γ, ∃ x₀ ∈ s,
        (∑ x ∈ s.erase x₀, (a x * (S.c γ x ^ 2 - S.c γ x₀ ^ 2)) • S.rho x φ) ≠ 0
    · obtain ⟨γ, hγ, x₀, hx₀, h⟩ := h
      refine ih (s.erase x₀) (Finset.erase_ssubset hx₀) _ ?_ h
      rw [← key γ hγ x₀ hx₀]
      exact N.sub_mem (N.smul_mem _ (hN _ _ hm)) (N.smul_mem _ hm)
    · push Not at h
      obtain ⟨x₀, hx₀⟩ : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hne (by simp)
      have hΓ : ∀ x ∈ s, x - x₀ ∈ Γ := by
        intro x hx
        refine (hd _).2 fun γ hγ => ?_
        have h1 := key γ hγ x hx
        have h2 := key γ hγ x₀ hx₀
        rw [h γ hγ x hx, sub_eq_zero] at h1
        rw [h γ hγ x₀ hx₀, sub_eq_zero, h1] at h2
        have h3 : S.c γ x ^ 2 = S.c γ x₀ ^ 2 := smul_left_injective ℂ hne h2
        have h4 := S.c_add_right γ (x - x₀) x₀
        rw [sub_add_cancel] at h4
        rw [h4, mul_pow] at h3
        exact mul_right_cancel₀ (pow_ne_zero 2 (c_ne S γ x₀)) (by rw [h3, one_mul])
      have hx : ∀ x ∈ s, S.rho x φ = ((S.c x₀ (x - x₀))⁻¹ * (al (x - x₀))⁻¹) • S.rho x₀ φ := by
        intro x hx
        have h1 := S.rho_rho x₀ (x - x₀) φ
        rw [hl _ (hΓ x hx), map_smul, add_sub_cancel] at h1
        rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (c_ne S _ _), one_smul]
      have hv : (∑ x ∈ s, a x • S.rho x φ)
          = (∑ x ∈ s, a x * ((S.c x₀ (x - x₀))⁻¹ * (al (x - x₀))⁻¹)) • S.rho x₀ φ := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun x hxs => ?_
        rw [hx x hxs, smul_smul]
      rw [hv] at hm hne
      have h0 := (N.smul_mem_iff (left_ne_zero_of_smul hne)).1 hm
      have h1 := hN (-x₀) _ h0
      rw [S.rho_rho, neg_add_cancel, S.rho_zero] at h1
      exact (N.smul_mem_iff (c_ne S _ _)).1 h1

theorem irreducible : ∀ {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
    (al : X → ℂ) (Γ : AddSubgroup X) (φ : M), SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ →
    Cyclic S φ →
    (∀ N : Submodule ℂ M, (∀ x, ∀ v ∈ N, S.rho x v ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ v : M, v ≠ 0 → Cyclic S v := by
  intro X M _ _ _ S al Γ φ hd hs hl hc
  have main : ∀ N : Submodule ℂ M, (∀ x, ∀ v ∈ N, S.rho x v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    rw [or_iff_not_imp_left]
    intro hb
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have hmem : v ∈ Submodule.span ℂ (Set.range fun x => S.rho x φ) := by
      rw [hc]; trivial
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    have hφ : φ ∈ N := by
      refine mem_of_sum S hd hs hl N hN f.support f ?_ ?_
      · rw [← hf] at hv
        exact hv
      · exact fun h => hv0 (hf.symm.trans h)
    rw [eq_top_iff, ← hc, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hN x φ hφ
  refine ⟨main, fun v hv => ?_⟩
  have hinv : ∀ x, ∀ w ∈ Submodule.span ℂ (Set.range fun x => S.rho x v),
      S.rho x w ∈ Submodule.span ℂ (Set.range fun x => S.rho x v) := by
    intro x w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, rfl⟩ := hw
      show S.rho x (S.rho y v) ∈ _
      rw [S.rho_rho]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  rcases main _ hinv with h | h
  · exfalso
    have : v ∈ Submodule.span ℂ (Set.range fun x => S.rho x v) :=
      Submodule.subset_span ⟨0, S.rho_zero v⟩
    rw [h] at this
    exact hv this
  · exact h

end GlobalTheory.CompanionTheory.FinHeis.Irred
