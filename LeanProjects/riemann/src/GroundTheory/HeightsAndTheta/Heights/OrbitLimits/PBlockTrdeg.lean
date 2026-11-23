import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsBlockTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal

namespace BlockTrdeg

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open scoped Classical

section Denominators

variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]

theorem exists_nat_mul_mem_range (ψ : MvPolynomial σ ℤ →+* L) {y : L}
    (hy : y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : L) * y ∈ ψ.range := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, one_ne_zero, ⟨X p, by rw [Nat.cast_one, one_mul]⟩⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ⟨(q.num : MvPolynomial σ ℤ), ?_⟩⟩
    rw [map_intCast, ← map_natCast (algebraMap ℚ L), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x + y) = m * (n * x) + n * (m * y) := by push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hnx) (mul_mem (natCast_mem _ _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x * y) = (n * x) * (m * y) := by push_cast; ring
    rw [e]
    exact mul_mem hnx hmy

theorem exists_nat_mul_mem_range_finset (ψ : MvPolynomial σ ℤ →+* L) (s : Finset L)
    (hs : ∀ y ∈ s, y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ y ∈ s, (n : L) * y ∈ ψ.range := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨n, hn, hns⟩ := ih fun y hy ↦ hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨m, hm, hma⟩ := exists_nat_mul_mem_range ψ (hs a (Finset.mem_insert_self a s))
    refine ⟨n * m, mul_ne_zero hn hm, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) hma
    · rw [Nat.cast_mul, mul_comm (n : L), mul_assoc]
      exact mul_mem (natCast_mem _ _) (hns y hy)

end Denominators

section Grading

variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

abbrev Forgotten (κ : K → K') : Type := {k' : K' // k' ∉ Set.range κ}

def forgetWeight (κ : K → K') : (Σ k', ι' k') → (Forgotten κ → ℕ) :=
  fun q k ↦ if q.1 = k.1 then 1 else 0

theorem weight_forgetWeight (κ : K → K') (m : (Σ k', ι' k') →₀ ℕ) (k : Forgotten κ) :
    Finsupp.weight (forgetWeight (ι' := ι') κ) m k = ∑ i, m ⟨k.1, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k.1]
  · simp [forgetWeight]
  · intro b _ hb
    simp [forgetWeight, hb]
  · simp

theorem isHomogeneous_forgetWeight (κ : K → K') {P : Ideal (MRing ι')} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (forgetWeight (ι' := ι') κ)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := hS x hx
  refine ⟨fun k ↦ a k.1, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_⟩
  intro d hd
  funext k
  rw [weight_forgetWeight]
  exact ha d (mem_support_iff.mpr hd) k.1

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem isWeightedHomogeneous_rename (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : ∀ p, (v p).1 ∈ Set.range κ) (g : MvPolynomial (Σ k, ι k) ℤ) :
    IsWeightedHomogeneous (forgetWeight κ) (rename v g) 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact isWeightedHomogeneous_C _ _
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p q hp =>
    rw [map_mul, rename_X]
    have h0 : forgetWeight κ (v q) = 0 := by
      funext k
      simp only [forgetWeight, Pi.zero_apply]
      rw [if_neg]
      intro h
      exact k.2 (h ▸ hv q)
    have := hp.mul (isWeightedHomogeneous_X ℤ (forgetWeight κ) (v q))
    rwa [h0, add_zero] at this

def forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1) (a : Forgotten κ →₀ ℕ) : MRing ι' :=
  ∏ k, X ⟨k.1, i k⟩ ^ a k

omit [∀ k, Fintype (ι' k)] in

theorem isWeightedHomogeneous_forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1)
    (a : Forgotten κ →₀ ℕ) :
    IsWeightedHomogeneous (forgetWeight κ) (forgetMonomial κ i a) ⇑a := by
  have := IsWeightedHomogeneous.prod Finset.univ (fun k ↦ (X ⟨k.1, i k⟩ : MRing ι') ^ a k)
    (fun k ↦ a k • forgetWeight κ ⟨k.1, i k⟩)
    fun k _ ↦ (isWeightedHomogeneous_X ℤ (forgetWeight κ) _).pow (a k)
  unfold forgetMonomial
  convert this using 1
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [forgetWeight]
  · intro b _ hb
    rw [Pi.smul_apply, forgetWeight, if_neg (fun h ↦ hb (Subtype.ext h)), smul_zero]
  · simp

end Grading

section Independence

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
  {L : Type} [Field L] [Algebra ℚ L] {φ : MRing ι' →+* L}

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem algebraicIndependent_forgotten (hv : ∀ p, (v p).1 = κ p.1) (hP : IsMultiHomogIdeal P')
    (hprime : P'.IsPrime) (hker : RingHom.ker φ = P') (i : ∀ k : Forgotten κ, ι' k.1)
    (hi : ∀ k, (X ⟨k.1, i k⟩ : MRing ι') ∉ P') (S : Subalgebra ℚ L)
    (hS : S ≤ adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) :
    AlgebraicIndependent S (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) := by
  rw [algebraicIndependent_iff]
  intro p hp
  set ψ : MvPolynomial (Σ k, ι k) ℤ →+* L := φ.comp (rename v).toRingHom with hψ
  have hA : adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) = adjoin ℚ (Set.range fun p ↦ ψ (X p)) := by
    simp [ψ]
  obtain ⟨N, hN, hNs⟩ := exists_nat_mul_mem_range_finset ψ (p.support.image fun a ↦ ((coeff a p : S) : L)) (by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hA]
    exact hS (coeff a p).2)
  choose g hg using fun a : p.support ↦ RingHom.mem_range.mp (hNs _ (Finset.mem_image_of_mem _ a.2))
  set H : MRing ι' := ∑ a : p.support, rename v (g a) * forgetMonomial κ i a.1 with hHdef
  have hH : H ∈ P' := by
    rw [← hker, RingHom.mem_ker]
    have e1 : φ H = (N : L) * aeval (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) p := by
      rw [hHdef, map_sum, aeval_def, eval₂_eq', Finset.mul_sum, ← Finset.sum_coe_sort p.support]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [map_mul, show φ (rename v (g a)) = ψ (g a) from rfl, hg a, forgetMonomial, map_prod]
      simp only [map_pow, mul_assoc]
      rfl
    rw [e1, hp, mul_zero]
  refine MvPolynomial.ext _ _ fun a ↦ ?_
  rw [coeff_zero]
  by_cases ha : a ∈ p.support
  swap
  · exact notMem_support_iff.mp ha
  have hhom : ∀ b : p.support, IsWeightedHomogeneous (forgetWeight κ)
      (rename v (g b) * forgetMonomial κ i b.1) ⇑b.1 := by
    intro b
    have := (isWeightedHomogeneous_rename κ (fun p ↦ ⟨p.1, (hv p).symm⟩) (g b)).mul
      (isWeightedHomogeneous_forgetMonomial κ i b.1)
    rwa [zero_add] at this
  have hcomp := weightedHomogeneousComponent_mem_of_mem ℤ (forgetWeight κ)
    (isHomogeneous_forgetWeight κ hP) hH (⇑a)
  have e2 : weightedHomogeneousComponent (forgetWeight κ) (⇑a) H =
      rename v (g ⟨a, ha⟩) * forgetMonomial κ i a := by
    rw [hHdef, map_sum, Finset.sum_eq_single ⟨a, ha⟩]
    · exact (hhom ⟨a, ha⟩).weightedHomogeneousComponent_same
    · intro b _ hb
      exact (hhom b).weightedHomogeneousComponent_ne _
        (fun h ↦ hb (Subtype.ext (DFunLike.coe_injective h).symm))
    · simp
  rw [e2] at hcomp
  rcases hprime.mem_or_mem hcomp with h1 | h1
  · rw [← hker, RingHom.mem_ker] at h1
    have h2 : (N : L) * ((coeff a p : S) : L) = 0 := by
      rw [← hg ⟨a, ha⟩]
      exact h1
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    have h3 := (mul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hN)
    exact_mod_cast h3
  · exfalso
    have := hprime
    rw [forgetMonomial] at h1
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
    exact hi k (hprime.mem_of_pow_mem _ hk)

end Independence

theorem proof : Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' L _ _ φ hκv hP hker
  obtain ⟨hκ, -, hv, -⟩ := hκv
  choose i hi using fun k : Forgotten κ ↦ hP.2.2 k.1
  set A := adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) with hAdef
  set B := adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)) with hBdef
  have : FaithfulSMul ℚ A :=
    (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective
  obtain ⟨τ, x, hx⟩ := exists_isTranscendenceBasis' ℚ A
  set b₀ : τ → L := A.val ∘ x with hb₀def
  have hb₀ : AlgebraicIndependent ℚ b₀ := hx.1.map' Subtype.val_injective
  have hSA : adjoin ℚ (Set.range b₀) ≤ A := adjoin_le (Set.range_subset_iff.mpr fun j ↦ (x j).2)
  have he := algebraicIndependent_forgotten hv hP.2.1 hP.1 hker i hi _ hSA
  have hind : AlgebraicIndependent ℚ (Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀) :=
    hb₀.sumElim he
  have hAB : A ≤ B := adjoin_mono (Set.range_subset_iff.mpr fun p ↦ ⟨v p, rfl⟩)
  have hmem : ∀ j, Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀ j ∈ B := by
    rintro (k | j)
    · exact subset_adjoin ⟨_, rfl⟩
    · exact hAB (x j).2
  have hy : AlgebraicIndependent ℚ (fun j ↦ (⟨_, hmem j⟩ : B)) := AlgebraicIndependent.of_comp B.val hind
  have hle := hy.cardinalMk_le_trdeg
  have hcard : ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) = #(Forgotten κ) := by
    rw [Cardinal.mk_fintype, Fintype.card_subtype_compl, Set.card_range_of_injective hκ]
  rw [← hx.cardinalMk_eq_trdeg, hcard, add_comm, ← lift_id #(Forgotten κ), ← lift_id #τ, ← mk_sum]
  exact hle

end BlockTrdeg

end GroundTheory.Heights₂.Heights
