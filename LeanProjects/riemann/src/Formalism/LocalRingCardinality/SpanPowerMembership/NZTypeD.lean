import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open MonoidAlgebra

variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

def tens (x : ∀ i, MonoidAlgebra k (G i)) : MonoidAlgebra k (∀ i, G i) :=
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g => ∏ i, (x i).coeff (g i)

theorem tens_coeff (x : ∀ i, MonoidAlgebra k (G i)) (g : ∀ i, G i) :
    (tens x).coeff g = ∏ i, (x i).coeff (g i) := rfl

theorem coeff_mul_fintype {Γ : Type} [Group Γ] [Fintype Γ] (x y : MonoidAlgebra k Γ) (g : Γ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

theorem tens_mul (x y : ∀ i, MonoidAlgebra k (G i)) : tens x * tens y = tens fun i => x i * y i := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype, tens_coeff]
  simp only [tens_coeff, coeff_mul_fintype, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

theorem tens_eq_zero (x : ∀ i, MonoidAlgebra k (G i)) (i : I) (h : x i = 0) : tens x = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [tens_coeff]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)

theorem tens_ne_zero (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i, x i ≠ 0) : tens x ≠ 0 := by
  have h1 : ∀ i, ∃ g : G i, (x i).coeff g ≠ 0 := fun i => by
    by_contra hc
    push Not at hc
    exact h i (MonoidAlgebra.coeff_injective (Finsupp.ext hc))
  choose g hg using h1
  intro h0
  have := congrArg (fun z => z.coeff g) h0
  simp only [tens_coeff] at this
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => hg i) this

theorem tens_single [DecidableEq I] (g : ∀ i, G i) : tens (fun i => (single (g i) 1 : MonoidAlgebra k (G i))) = single g 1 := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext h
  rw [tens_coeff, MonoidAlgebra.coeff_single_apply]
  simp only [MonoidAlgebra.coeff_single_apply]
  by_cases e : g = h
  · subst e; simp
  · rw [if_neg e]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem commute_of_single {Γ : Type} [Group Γ] (z : MonoidAlgebra k Γ)
    (h : ∀ g : Γ, z * single g 1 = single g 1 * z) (a : MonoidAlgebra k Γ) : z * a = a * z := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]
  | single g r =>
    have e : (single g r : MonoidAlgebra k Γ) = r • single g 1 := by rw [smul_single', mul_one]
    rw [e, mul_smul_comm, smul_mul_assoc, h]

theorem tens_central (x : ∀ i, MonoidAlgebra k (G i)) (h : ∀ i a, x i * a = a * x i)
    (a : MonoidAlgebra k (∀ i, G i)) : tens x * a = a * tens x := by
  classical
  refine commute_of_single _ (fun g => ?_) a
  rw [← tens_single, tens_mul, tens_mul]
  exact congrArg tens (funext fun i => h i _)

variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)

open Classical in

def eSum : MonoidAlgebra k (∀ i, G i) := ∑ a : (∀ i, L i), if S a then tens (fun i => E i (a i)) else 0

variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)

include hcen in
theorem eSum_central (a : MonoidAlgebra k (∀ i, G i)) : eSum E S * a = a * eSum E S := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs
  · exact tens_central _ (fun i => hcen i _) a
  · simp

include hidem horth in
theorem tens_mul_tens (a b : ∀ i, L i) : tens (fun i => E i (a i)) * tens (fun i => E i (b i)) =
    open Classical in if a = b then tens (fun i => E i (a i)) else 0 := by
  rw [tens_mul]
  split_ifs with e
  · subst e; exact congrArg tens (funext fun i => hidem i _)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp e
    exact tens_eq_zero _ i (horth i _ _ hi)

include hidem horth in
theorem eSum_mul_tens (b : ∀ i, L i) : eSum E S * tens (fun i => E i (b i)) =
    open Classical in if S b then tens (fun i => E i (b i)) else 0 := by
  classical
  unfold eSum
  rw [Finset.sum_mul, Finset.sum_eq_single b]
  · split_ifs
    · rw [tens_mul_tens E hidem horth, if_pos rfl]
    · simp
  · intro a _ hab
    split_ifs
    · rw [tens_mul_tens E hidem horth, if_neg hab]
    · simp
  · intro h; exact absurd (Finset.mem_univ b) h

include hidem horth in
theorem eSum_idem : eSum E S * eSum E S = eSum E S := by
  classical
  conv_lhs => rhs; unfold eSum
  rw [Finset.mul_sum]
  unfold eSum
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · have := eSum_mul_tens E S hidem horth b
    rw [if_pos hb] at this
    exact this
  · simp

include hidem horth in
theorem eSum_ne_zero (b : ∀ i, L i) (hb : S b) (hne : ∀ i, E i (b i) ≠ 0) : eSum E S ≠ 0 := by
  intro h0
  have := eSum_mul_tens E S hidem horth b
  rw [if_pos hb, h0, zero_mul] at this
  exact tens_ne_zero _ hne this.symm

theorem eSum_coeff (g : ∀ i, G i) : (eSum E S).coeff g =
    open Classical in ∑ a : (∀ i, L i), if S a then ∏ i, (E i (a i)).coeff (g i) else 0 := by
  classical
  unfold eSum
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rfl
  · rfl

theorem exists_char_comm (Z : Type) [CommRing Z] [Algebra ℂ Z] [FiniteDimensional ℂ Z] (e : Z)
    (hi : e * e = e) (h0 : e ≠ 0) : ∃ ω : Z →ₐ[ℂ] ℂ, ω e = 1 := by
  have hne : Ideal.span {1 - e} ≠ ⊤ := by
    intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)
    apply h0
    calc e = (c * (1 - e)) * e := by rw [hc, one_mul]
      _ = c * (e - e * e) := by ring
      _ = 0 := by rw [hi, sub_self, mul_zero]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let _ : Field (Z ⧸ m) := Ideal.Quotient.field m
  have : FiniteDimensional ℂ (Z ⧸ m) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℂ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := Z ⧸ m)
  let φ : ℂ ≃ₐ[ℂ] (Z ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (Z ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), ?_⟩
  have h1 : Ideal.Quotient.mkₐ ℂ m e = 1 := by
    have : Ideal.Quotient.mk m (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self _))
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  show φ.symm (Ideal.Quotient.mkₐ ℂ m e) = 1
  rw [h1, map_one]

theorem exists_char {Γ : Type} [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ)
    (hc : e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ Γ)) (hi : e * e = e) (h0 : e ≠ 0) :
    ∃ ω : Subalgebra.center ℂ (MonoidAlgebra ℂ Γ) →ₐ[ℂ] ℂ, ω ⟨e, hc⟩ = 1 := by
  have hfd : FiniteDimensional ℂ (MonoidAlgebra ℂ Γ) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  exact exists_char_comm _ ⟨e, hc⟩ (Subtype.ext hi) (fun h => h0 (congrArg Subtype.val h))

end Formalism.BasicNotions.Examples₂.NZ
