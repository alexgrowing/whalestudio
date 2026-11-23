import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HermitianCoefficientIdentityOne

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

private theorem unit_mul_lemma {a c : K} (ha : IsUnitIn S a) (hc : IsUnitIn S c) :
    IsUnitIn S (a * c) :=
  And.intro (mul_ne_zero ha.1 hc.1)
    (And.intro (S.mul_mem ha.2.1 hc.2.1) (by rw [mul_inv]; exact S.mul_mem ha.2.2 hc.2.2))

theorem absorb (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {e : ι → ℕ} {i₀ : ι} (x : ι → K) (hx : ∀ i, x i ∈ S) :
    ∀ T : Finset ι, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : ι → V,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧
      (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro _ _ b ho hu
    exact ⟨b, ho, hu, by simp, fun _ _ _ => rfl, rfl, fun _ => Iff.rfl⟩
  · intro a T haT ih hi₀ hlt b ho hu
    have hi₀T : i₀ ∉ T := fun hm => hi₀ (Finset.mem_insert_of_mem hm)
    have hai₀ : i₀ ≠ a := by
      intro h'
      apply hi₀
      rw [h']
      exact Finset.mem_insert_self a T
    obtain ⟨c', ho', hu', hc'0, hc'k, hsp', hiff'⟩ :=
      ih hi₀T (fun j hj => hlt j (Finset.mem_insert_of_mem hj)) b ho hu
    have hc'a : c' a = b a := hc'k a (Ne.symm hai₀) haT
    have hlta : e i₀ < e a := hlt a (Finset.mem_insert_self a T)
    have hu0 : h (c' i₀) (c' i₀) ≠ 0 := unit_ne (hu' i₀)
    have hπ0 : π ≠ 0 := hπ.ne
    obtain ⟨d, hd⟩ : ∃ d, e a = e i₀ + d + 1 := ⟨e a - e i₀ - 1, by omega⟩
    have hs0 : (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹)⁻¹
        * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d) ∈ S :=
      S.mul_mem (hu' i₀).2.2 (S.mul_mem (S.mul_mem (S.mul_mem (hS.star_mem _ (hx a)) (hx a))
        (hu' a).2.1) (S.pow_mem hπ.mem d))
    have hY : IsUnitIn S (h ((1 : K) • c' i₀ + x a • c' a) ((1 : K) • c' i₀ + x a • c' a)
        * (π ^ e i₀)⁻¹) := by
      rw [form_pair (c' i₀) (c' a) (ho' i₀ a hai₀) (ho' a i₀ (Ne.symm hai₀))]
      have eq : (star (1 : K) * 1 * h (c' i₀) (c' i₀) + star (x a) * x a * h (c' a) (c' a))
          * (π ^ e i₀)⁻¹ = (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹) * (1 + π * ((h (c' i₀) (c' i₀)
          * (π ^ e i₀)⁻¹)⁻¹ * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d))) := by
        rw [hd, star_one]
        field_simp
        ring
      rw [eq]
      exact unit_mul_lemma (hu' i₀) (hπ.rad _ hs0)
    obtain ⟨c, ho2, hu2, hc0, hck, hsp2, hiff2⟩ :=
      rot2 hS hπ hs ho' hu' hai₀ hlta.le S.one_mem (hx a) hY
    refine ⟨c, ho2, hu2, ?_, ?_, hsp2.trans hsp', fun v => (hiff2 v).trans (hiff' v)⟩
    · rw [hc0, hc'0, hc'a, one_smul, Finset.sum_insert haT]
      abel
    · intro k hk0 hkT
      have hka : k ≠ a := by
        intro h'
        apply hkT
        rw [h']
        exact Finset.mem_insert_self a T
      have hkT' : k ∉ T := fun h' => hkT (Finset.mem_insert_of_mem h')
      rw [hck k hk0 hka, hc'k k hk0 hkT']

end

end Formalism.L2.SG.Pf.G3
