import Mathlib
open Polynomial

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem algebraMap_quot_bijective (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  haveI : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k (A ⧸ P)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem maximal_part (P : Ideal A) (hP : P.IsMaximal) :
    Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0 := by
  have hb := algebraMap_quot_bijective (k := k) P
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hb
  refine ⟨?_, ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩⟩
  · rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · change u ∈ P ↔ e.symm (Ideal.Quotient.mkₐ k P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]

theorem exists_sub_mem (P : Ideal A) [P.IsMaximal] (a : A) :
    ∃ c : k, a - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quot_bijective (k := k) P).2 (Ideal.Quotient.mk P a)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at hc
  rw [← P.neg_mem_iff, neg_sub]
  exact hc

theorem span_sup_mul_eq (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (x : A) (hx : x ∈ I)
    (hxP : x ∉ I * P) : Ideal.span {x} ⊔ I * P = I := by
  have hKI : Ideal.span {x} ⊔ I * P ≤ I :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) Ideal.mul_le_left
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hKI
  have hPL : I * P ≤ I * L := hL ▸ le_sup_right
  have hLP : P ≤ L := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (show I ≠ 0 from hI)).1
    (Ideal.dvd_iff_le.2 hPL))
  by_cases hLt : L = ⊤
  · rw [hL, hLt, Ideal.mul_top]
  · have := hP.eq_of_le hLt hLP
    subst this
    exact absurd (hL ▸ (le_sup_left : Ideal.span {x} ≤ _) (Ideal.mem_span_singleton_self x)) hxP

theorem rank_quot_mul_maximal (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) :
    Module.rank k (A ⧸ (I * P)) = Module.rank k (A ⧸ I) + 1 := by
  haveI := hP
  have hne : I * P ≠ I := by
    intro h
    have h2 : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact hP.ne_top (mul_left_cancel₀ (show I ≠ 0 from hI) h2)
  obtain ⟨x, hx, hxP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm Ideal.mul_le_left h)
  let f : (A ⧸ (I * P)) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_left : I * P ≤ I)).toLinearMap
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  set v : A ⧸ (I * P) := Ideal.Quotient.mk _ x with hvdef
  have hv0 : v ≠ 0 := fun h => hxP (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hker : LinearMap.ker f = k ∙ v := by
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hy : y ∈ I := by
        have h0 : f (Ideal.Quotient.mk _ y) = 0 := hz
        exact Ideal.Quotient.eq_zero_iff_mem.1 h0
      have hyK : y ∈ Ideal.span {x} ⊔ I * P := by
        rw [span_sup_mul_eq I P hI hP x hx hxP]; exact hy
      obtain ⟨a', ha', z', hz', hsum⟩ := Submodule.mem_sup.1 hyK
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
      obtain ⟨c, hc⟩ := exists_sub_mem (k := k) P a
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [← hsum, hvdef, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        Ideal.Quotient.eq]
      have h3 : algebraMap k A c * x - (a * x + z') = -((a - algebraMap k A c) * x) - z' := by
        ring
      rw [h3]
      refine Ideal.sub_mem _ ((I * P).neg_mem ?_) hz'
      rw [mul_comm I P]
      exact Ideal.mul_mem_mul hc hx
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      show f v = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  have h1 := LinearMap.rank_range_add_rank_ker f
  rw [LinearMap.range_eq_top.2 hf, rank_top, hker] at h1
  have hv1 : Module.rank k (k ∙ v) = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton hv0]; simp
  rw [← h1, hv1]

end DedekindCodim
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem rank_quot_top : Module.rank k (A ⧸ (⊤ : Ideal A)) = 0 := by
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact rank_subsingleton' k _

theorem maximal_of_prime {p : Ideal A} (hp : Prime p) : p ≠ ⊥ ∧ p.IsMaximal := by
  have hne : p ≠ ⊥ := hp.ne_zero
  exact ⟨hne, ((Ideal.prime_iff_isPrime hne).1 hp).isMaximal hne⟩

theorem rank_quot_lt (J : Ideal A) (hJ : J ≠ ⊥) : Module.rank k (A ⧸ J) < Cardinal.aleph0 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top]; exact Cardinal.aleph0_pos
  | h₃ a p ha hp ih =>
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    rw [mul_comm, rank_quot_mul_maximal a p ha hpm]
    exact Cardinal.add_lt_aleph0 (ih ha) Cardinal.one_lt_aleph0

theorem rank_quot_mul (J : Ideal A) (hJ : J ≠ ⊥) : ∀ I : Ideal A, I ≠ ⊥ →
    Module.rank k (A ⧸ (I * J)) = Module.rank k (A ⧸ I) + Module.rank k (A ⧸ J) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    intro I _
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top, Ideal.mul_top, add_zero]
  | h₃ a p ha hp ih =>
    intro I hI
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    have hIa : I * a ≠ ⊥ := mul_ne_zero (show I ≠ 0 from hI) ha
    rw [show I * (p * a) = (I * a) * p by ring, rank_quot_mul_maximal _ p hIa hpm, ih ha I hI,
      mul_comm p a, rank_quot_mul_maximal a p ha hpm, add_assoc]

theorem finite_quot (I : Ideal A) (hI : I ≠ ⊥) : Module.Finite k (A ⧸ I) :=
  Module.rank_lt_aleph0_iff.1 (rank_quot_lt I hI)

theorem finrank_quot_mul (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J) := by
  haveI := finite_quot (k := k) I hI
  haveI := finite_quot (k := k) J hJ
  haveI := finite_quot (k := k) (I * J) (mul_ne_zero (show I ≠ 0 from hI) (show J ≠ 0 from hJ))
  have h := rank_quot_mul (k := k) J hJ I hI
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem eq_of_le_of_finrank_le (I J : Ideal A) (hI : I ≠ ⊥) (hIJ : I ≤ J)
    (hr : Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J)) : I = J := by
  obtain ⟨L, rfl⟩ := Ideal.dvd_iff_le.2 hIJ
  have hJ : J ≠ ⊥ := fun h => hI (by rw [h]; exact (zero_mul L : (0 : Ideal A) * L = 0))
  have hL : L ≠ ⊥ := fun h => hI (by rw [h]; exact (mul_zero J : J * (0 : Ideal A) = 0))
  rw [finrank_quot_mul J L hJ hL] at hr
  have h0 : Module.finrank k (A ⧸ L) = 0 := by omega
  haveI := finite_quot (k := k) L hL
  have hs : Subsingleton (A ⧸ L) := Module.finrank_zero_iff.1 h0
  rw [Ideal.Quotient.subsingleton_iff.1 hs, Ideal.mul_top]

theorem dedekind_finiteType_codim : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A],
    (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧
      ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J) := by
  intro k A _ _ _ _ _ _ _
  exact ⟨fun I hI => finite_quot I hI, fun P hP => maximal_part P hP,
    fun I J hI hJ => finrank_quot_mul I J hI hJ,
    fun I J hI hIJ hr => eq_of_le_of_finrank_le I J hI hIJ hr⟩

end DedekindCodim
end GlobalTheory
