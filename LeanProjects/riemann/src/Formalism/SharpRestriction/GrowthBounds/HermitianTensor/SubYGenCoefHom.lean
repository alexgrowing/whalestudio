import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem midI_val (r : ℕ) (j : Fin r) : (midI r j).val = j.val + 1 := by
  simp [midI]

theorem midI_inj (r : ℕ) (i j : Fin r) : midI r i = midI r j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [midI_val, midI_val] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

theorem midI_lt (r : ℕ) {i j : Fin r} (h : i < j) : midI r i < midI r j := by
  rw [Fin.lt_iff_val_lt_val, midI_val, midI_val]
  have := Fin.lt_iff_val_lt_val.mp h
  omega

theorem midI_pos (r : ℕ) (j : Fin r) : (0 : Fin (r + 1 + 1)) < midI r j := by
  rw [Fin.lt_def, midI_val]
  simp

theorem midOf_midI (r : ℕ) (j : Fin r) : midOf (midI r j) = some j := by
  have hv := midI_val r j
  have hj := j.isLt
  unfold midOf
  rw [dif_pos (by rw [hv]; exact ⟨Nat.succ_pos _, by omega⟩)]
  congr 1

theorem midOf_cases {r : ℕ} (t : Fin (r + 1 + 1)) :
    (∃ j, t = midI r j) ∨ (midOf t = none ∧ (t = 0 ∨ t = Fin.last (r + 1))) := by
  have ht := t.isLt
  by_cases h : 0 < t.val ∧ t.val < r + 1
  · left
    refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
    ext
    rw [midI_val]
    dsimp only
    omega
  · right
    refine ⟨by unfold midOf; rw [dif_neg h], ?_⟩
    by_cases h0 : t.val = 0
    · left
      exact Fin.ext (by simp [h0])
    · right
      exact Fin.ext (by simp; omega)

theorem midOf_none_ne {r : ℕ} {t : Fin (r + 1 + 1)} (h : midOf t = none) (j : Fin r) : midI r j ≠ t := by
  rintro rfl
  rw [midOf_midI] at h
  exact Option.some_ne_none _ h

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

theorem subY_X_none (A : Type) [CommRing A] (r : ℕ) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    subY A r (X (a, t)) = X (a, t) := by
  simp only [subY, aeval_X, h]

theorem subY_C (A : Type) [CommRing A] (r : ℕ) (a : A) : subY A r (C a) = C (C a) := by
  simp [subY]

section MAH

variable {R S1 S2 σ : Type} [CommRing R] [CommRing S1] [CommRing S2] [Algebra R S1] [Algebra R S2]

theorem mAH_coeff (f : S1 →ₐ[R] S2) (p : MvPolynomial σ S1) (u : σ →₀ ℕ) : coeff u (mapAlgHom f p) = f (coeff u p) := by
  show coeff u (map (f : S1 →+* S2) p) = _
  rw [coeff_map]
  rfl

theorem mAH_C (f : S1 →ₐ[R] S2) (b : S1) : mapAlgHom f (C b : MvPolynomial σ S1) = C (f b) := by
  show map (f : S1 →+* S2) (C b) = _
  rw [map_C]
  rfl

theorem mAH_X (f : S1 →ₐ[R] S2) (w : σ) : mapAlgHom f (X w : MvPolynomial σ S1) = X w := by
  show map (f : S1 →+* S2) (X w) = _
  rw [map_X]

end MAH

theorem mAH_subY_mid {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a : Fin (r + 1 + 1)) (j : Fin r) :
    mapAlgHom f (subY A r (X (a, midI r j))) = ∑ i : Fin r, C (f (X (i, j))) * X (a, midI r i) := by
  rw [subY_X_mid]
  simp only [map_sum, map_mul, mAH_C, mAH_X]

theorem mAH_subY_none {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    mapAlgHom f (subY A r (X (a, t))) = X (a, t) := by
  rw [subY_X_none A r a t h, mAH_X]

section Coef

variable {A : Type} [CommRing A] {r : ℕ} {σ : Type}

def CoefHom (μ : Fin r → ℕ) (h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) : Prop :=
  ∀ u, IsWeightedHomogeneous (colW r r) (coeff u h) μ

theorem CoefHom.sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) (μ : Fin r → ℕ)
    (h : ∀ i ∈ s, CoefHom μ (f i)) : CoefHom μ (∑ i ∈ s, f i) := by
  intro u
  rw [coeff_sum]
  exact IsWeightedHomogeneous.sum _ _ _ (fun i hi => h i hi u)

theorem CoefHom.mul {μ μ' : Fin r → ℕ} {h1 h2 : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)}
    (a : CoefHom μ h1) (b : CoefHom μ' h2) : CoefHom (μ + μ') (h1 * h2) := by
  classical
  intro u
  rw [coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (a x.1).mul (b x.2))

theorem CoefHom.ofC {μ : Fin r → ℕ} {b : MvPolynomial (Fin r × Fin r) A} (hb : IsWeightedHomogeneous (colW r r) b μ) :
    CoefHom (σ := σ) μ (C b) := by
  classical
  intro u
  rw [coeff_C]
  split_ifs
  · exact hb
  · exact isWeightedHomogeneous_zero _ _ _

theorem CoefHom.ofX (w : σ) : CoefHom (A := A) (r := r) 0 (X w) := by
  classical
  intro u
  rw [coeff_X']
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem CoefHom.one : CoefHom (A := A) (r := r) (σ := σ) 0 1 := by
  classical
  intro u
  rw [coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · intro d hd
    simp at hd

theorem CoefHom.pow {μ : Fin r → ℕ} {h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)} (a : CoefHom μ h) (n : ℕ) :
    CoefHom (n • μ) (h ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact CoefHom.one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul a

theorem CoefHom.prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A))
    (μ : ι → Fin r → ℕ) (h : ∀ i ∈ s, CoefHom (μ i) (f i)) : CoefHom (∑ i ∈ s, μ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact CoefHom.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end Coef

theorem subY_gen_coefHom (A : Type) [CommRing A] (r : ℕ) (w : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    CoefHom (fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) (subY A r (X w)) := by
  obtain ⟨a, t⟩ := w
  rcases midOf_cases t with ⟨j, rfl⟩ | ⟨hn, -⟩
  · rw [subY_X_mid]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, midI r j) (midI r j')) = colW r r (j, j) := by
      funext j'
      simp only [colW, Pi.single_apply, midI_inj]
    rw [hf]
    apply CoefHom.sum
    intro i _
    have h := (CoefHom.ofC (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (isWeightedHomogeneous_X A (colW r r) (i, j))).mul (CoefHom.ofX (A := A) (r := r) (a, midI r i))
    rw [add_zero] at h
    exact h
  · rw [subY_X_none _ _ _ _ hn]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, t) (midI r j')) = 0 := by
      funext j'
      simp [colW, Pi.single_apply, midOf_none_ne hn j']
    rw [hf]
    exact CoefHom.ofX _

theorem subY_coefHom (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν) :
    CoefHom (fun j => ν (midI r j)) (subY A r v) := by
  classical
  rw [v.as_sum, map_sum]
  apply CoefHom.sum
  intro m hm
  have hw : Finsupp.weight (colW (r + 1 + 1) (r + 1 + 1)) m = ν := hv (mem_support_iff.mp hm)
  rw [monomial_eq, map_mul, subY_C, Finsupp.prod, map_prod]
  have hP : CoefHom (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j))
      (∏ w ∈ m.support, subY A r (X w ^ m w)) := by
    apply CoefHom.prod
    intro w _
    rw [map_pow]
    exact (subY_gen_coefHom A r w).pow _
  have hC : CoefHom (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1)) (0 : Fin r → ℕ) (C (C (coeff m v))) := by
    apply CoefHom.ofC
    intro d hd
    rw [coeff_C] at hd
    split_ifs at hd with h0
    · subst h0
      simp
    · exact absurd rfl hd
  have h := hC.mul hP
  rw [zero_add] at h
  have hsum : (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) =
      fun j => ν (midI r j) := by
    funext j
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [hsum] at h
  exact h

theorem subY_inv (A : Type) [CommRing A] (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v) (l j : Fin r) (hlj : l < j)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    colAddGen A l j (coeff u (subY A r v)) = rename some (coeff u (subY A r v)) := by
  classical
  let Φ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (colAddGen A l j)
  let Ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (rename some)
  let θ : MvPolynomial (Option (Fin (r + 1 + 1) × Fin (r + 1 + 1))) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    aeval fun o => Option.elim o (C (X none)) fun w => Ψ (subY A r (X w))
  have hθn : θ (X none) = C (X none) := by
    simp [θ]
  have hθs : ∀ w, θ (X (some w)) = Ψ (subY A r (X w)) := fun w => by
    simp [θ]
  have h1 : Φ.comp (subY A r) = θ.comp (colAddGen A (midI r l) (midI r j)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp only [AlgHom.comp_apply, colAddGen_X]
    rcases midOf_cases t with ⟨j', rfl⟩ | ⟨hn, -⟩
    · rw [mAH_subY_mid]
      by_cases hj : j' = j
      · subst hj
        rw [if_pos rfl, map_add, map_mul, hθn, hθs, hθs, mAH_subY_mid, mAH_subY_mid, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_true, rename_X, map_add, map_mul]
        ring
      · rw [if_neg (fun h => hj ((midI_inj r j' j).mp h)), hθs, mAH_subY_mid]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_neg hj, rename_X]
    · rw [if_neg (midOf_none_ne hn j).symm, hθs, mAH_subY_none _ _ _ _ hn, mAH_subY_none _ _ _ _ hn]
  have h2 : Ψ.comp (subY A r) = θ.comp (rename some) := by
    apply MvPolynomial.algHom_ext
    intro w
    simp only [AlgHom.comp_apply, rename_X, hθs]
  have h3 : Φ (subY A r v) = Ψ (subY A r v) := by
    have e1 := congrArg (fun F => F v) h1
    have e2 := congrArg (fun F => F v) h2
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hv _ _ (midI_lt r hlj)]
  have h4 := congrArg (coeff u) h3
  simp only [Φ, Ψ, mAH_coeff] at h4
  exact h4

theorem subCoeffP : SubCoeffP := by
  intro A _ r ν v hv u
  rw [lsat_mem_dualWeyl] at hv ⊢
  exact ⟨subY_coefHom A r ν v hv.1 u, fun l j hlj => subY_inv A r v hv.2 l j hlj u⟩

end Formalism.MainNotions.flipOneThree.Pf.QB

end
