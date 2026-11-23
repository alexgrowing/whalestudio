import Formalism.SharpRestriction.GrowthBounds.RootWeights.MatrixSubstTransvectionMonomialOfFixed

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G

section mtch

variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)

open Classical in
theorem dividedPowerMonomial_eq_sum (k : ℕ) :
    divPowMono B LL S a b k m = ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
      monomial (shiftedExponent LL a b m (⇑f)) (rootShiftCoefficient B LL a b m (⇑f)) := by
  have sum_support_single_eq_lemma {σ ι : Type _} [Fintype ι] (f : ι →₀ ℕ) (g : ι → σ) :
      ∑ l ∈ f.support, Finsupp.single (g l) (f l) = ∑ l, Finsupp.single (g l) (f l) :=
    Finset.sum_subset (Finset.subset_univ _) fun l _ hl => by
      have h0 : f l = 0 := by simpa using hl
      rw [h0, Finsupp.single_zero]
  simp only [Formalism.MainNotions.G.divPowMono, shiftedExponent, rootShiftCoefficient, sourceVar, targetVar]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [sum_support_single_eq_lemma f, sum_support_single_eq_lemma f, Finset.prod_subset (Finset.subset_univ f.support)]
  intro l _ hl
  have h0 : f l = 0 := by simpa using hl
  simp [h0]

open Classical in
theorem sum_finsuppAntidiag_eq_sum_piFinset (k : ℕ) :
    ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
      monomial (shiftedExponent LL a b m (⇑f)) (rootShiftCoefficient B LL a b m (⇑f)) =
    ∑ p ∈ (Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1))).filter (fun p => ∑ l, p l = k),
      monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by
  have hcf : ∀ p : ι → ℕ, rootShiftCoefficient B LL a b m p ≠ 0 → ∀ l, p l ≤ m (sourceVar LL a b l) := by
    intro p hp l
    by_contra hlt
    push_neg at hlt
    apply hp
    unfold rootShiftCoefficient
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    unfold sourceVar at hlt
    split_ifs at hlt ⊢ with hv
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
    · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  have hmon : ∀ (s : ι × Fin n →₀ ℕ) (c : B),
      (monomial s c : MvPolynomial (ι × Fin n) B) ≠ 0 → c ≠ 0 :=
    fun s c h hc => h (by rw [hc, map_zero])
  have hsumS : ∀ p : ι → ℕ, (∀ l, l ∉ S → p l = 0) →
      ∑ l ∈ Finset.univ.filter (· ∈ S), p l = ∑ l, p l := by
    intro p hp
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => hp l ?_
    intro hS
    exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩)
  refine Finset.sum_bij_ne_zero (fun f _ _ => ⇑f) ?_ ?_ ?_ ?_
  · intro f hf hne
    rw [Finset.mem_finsuppAntidiag] at hf
    have hz : ∀ l, l ∉ S → f l = 0 := fun l hl => by
      by_contra h
      exact hl (Finset.mem_filter.mp (hf.2 (Finsupp.mem_support_iff.mpr h))).2
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun l => ?_, ?_⟩
    · rw [Nat.lt_succ_iff]
      by_cases hl : l ∈ S
      · rw [sourceExp, if_pos hl]
        exact hcf _ (hmon _ _ hne) l
      · rw [hz l hl]
        exact Nat.zero_le _
    · rw [← hsumS _ hz]
      exact hf.1
  · intro f₁ _ _ f₂ _ _ h
    exact DFunLike.coe_injective h
  · intro p hp hne
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hp
    have hle : ∀ l, p l ≤ sourceExp LL S a b m l := fun l => Nat.lt_succ_iff.mp (hp.1 l)
    have hz : ∀ l, l ∉ S → p l = 0 := fun l hl => by
      have h := hle l
      rw [sourceExp, if_neg hl] at h
      omega
    refine ⟨Finsupp.equivFunOnFinite.symm p, ?_, ?_, ?_⟩
    · rw [Finset.mem_finsuppAntidiag, Finsupp.coe_equivFunOnFinite_symm]
      refine ⟨by rw [hsumS _ hz]; exact hp.2, fun l hl => ?_⟩
      rw [Finsupp.mem_support_iff, Finsupp.coe_equivFunOnFinite_symm] at hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hS
      exact hl (hz l hS)
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact hne
    · exact Finsupp.coe_equivFunOnFinite_symm p
  · intro f _ _
    rfl

theorem sum_sourceExp_le : ∑ l : ι, sourceExp LL S a b m l ≤ m.sum fun _ e => e := by
  classical
  have hinj : ∀ x ∈ (Finset.univ : Finset ι), ∀ y ∈ (Finset.univ : Finset ι),
      sourceVar LL a b x = sourceVar LL a b y → x = y := by
    intro x _ y _ h
    have h1 := congrArg Prod.fst h
    rwa [sourceVar_fst, sourceVar_fst] at h1
  calc ∑ l : ι, sourceExp LL S a b m l ≤ ∑ l : ι, m (sourceVar LL a b l) :=
        Finset.sum_le_sum fun l _ => by unfold sourceExp; split_ifs <;> simp
    _ = ∑ v ∈ Finset.univ.image (sourceVar LL a b), m v := (Finset.sum_image hinj).symm
    _ ≤ ∑ v ∈ m.support, m v := Finset.sum_le_sum_of_ne_zero fun v _ h => Finsupp.mem_support_iff.mpr h
    _ = m.sum fun _ e => e := rfl

variable {R : Type*} [CommRing R] (φ : R →+* B)

theorem matrixSubst_transvection_monomial (N : ℕ) (hN : (m.sum fun _ e => e) < N) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      ∑ k ∈ Finset.range N, C (t ^ k) * divPowMono B LL S a b k m := by
  classical
  rw [matrixSubst_transvection_monomial_sum]
  have hmaps : ∀ p ∈ Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1)),
      (∑ l, p l) ∈ Finset.range N := by
    intro p hp
    rw [Fintype.mem_piFinset] at hp
    rw [Finset.mem_range]
    calc ∑ l, p l ≤ ∑ l, sourceExp LL S a b m l :=
          Finset.sum_le_sum fun l _ => by have := Finset.mem_range.mp (hp l); omega
      _ ≤ _ := sum_sourceExp_le LL S a b m
      _ < N := hN
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dividedPowerMonomial_eq_sum, sum_finsuppAntidiag_eq_sum_piFinset, Finset.mul_sum]
  refine Finset.sum_congr (by ext p; simp only [Finset.mem_filter]) fun p hp => ?_
  have hk : ∑ l, p l = k := (Finset.mem_filter.mp hp).2
  rw [hk]

theorem map_dividedPowerMonomial (k : ℕ) :
    MvPolynomial.map φ (divPowMono R LL S a b k m) = divPowMono B LL S a b k m := by
  unfold Formalism.MainNotions.G.divPowMono
  rw [map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h : ∀ l, φ (if LL.vec l then ((m (l, b)).choose (f l) : R) else (-1 : R) ^ (f l) * ((m (l, a)).choose (f l) : R)) =
      (if LL.vec l then ((m (l, b)).choose (f l) : B) else (-1 : B) ^ (f l) * ((m (l, a)).choose (f l) : B)) :=
    fun l => by split_ifs <;> simp
  simp only [MvPolynomial.map_monomial, map_prod, h]

theorem dividedPower_monomial (k : ℕ) (c : R) :
    divPow R LL S a b k (monomial m c) = c • divPowMono R LL S a b k m := by
  have h1 : (monomial m c : MvPolynomial (ι × Fin n) R) = c • MvPolynomial.basisMonomials (ι × Fin n) R m := by
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul]
  unfold Formalism.MainNotions.G.divPow
  rw [Module.Basis.constr_basis]

end mtch

theorem transvectionExpansion : TransvectionExpansion := by
  unfold TransvectionExpansion
  intro R B _ _ ι _ LL n S φ a b _ t F N hF
  have key : ∀ v ∈ F.support,
      matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial v (coeff v F)) =
        ∑ k ∈ Finset.range N, C (t ^ k) * MvPolynomial.map φ (Formalism.MainNotions.G.divPow R LL S a b k (monomial v (coeff v F))) := by
    intro v hv
    have hv' : (v.sum fun _ e => e) < N := lt_of_le_of_lt (MvPolynomial.le_totalDegree hv) hF
    have hmono : (monomial v (coeff v F) : MvPolynomial (ι × Fin n) R) = C (coeff v F) * monomial v 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    have hL : matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial v (coeff v F)) =
        C (φ (coeff v F)) * ∑ k ∈ Finset.range N, C (t ^ k) * Formalism.MainNotions.G.divPowMono B LL S a b k v := by
      rw [hmono, map_mul, matrixSubst_C, matrixSubst_transvection_monomial LL S a b t v φ N hv']
    rw [hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dividedPower_monomial, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_dividedPowerMonomial]
    ring
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine (Finset.sum_congr rfl key).trans ?_
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

end Formalism.MainNotions.G.GLWeightTheory
