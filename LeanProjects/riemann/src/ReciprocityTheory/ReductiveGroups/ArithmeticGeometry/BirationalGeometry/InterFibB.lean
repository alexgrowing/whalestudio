import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable (ι) in

def blkW : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_blkW (β : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkW ι) β k = ∑ i, β ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [blkW, Pi.single_apply]

theorem isWeightedHomogeneous_map_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) s) a := by
  intro d hd
  rw [coeff_map] at hd
  have hs' : d ∈ s.support := by
    rw [mem_support_iff]
    intro h0
    apply hd
    simp [h0]
  funext k
  rw [weight_blkW]
  exact hs d hs' k

theorem diag_prod (d : ℕ) : ∀ e : (Σ k, ι k) → ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = d) →
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ e p = eval (segre z) G := by
  induction d with
  | zero =>
    intro e he
    refine ⟨1, by simp, fun z => ?_⟩
    have h0 : ∀ p, e p = 0 := by
      intro p
      have := he p.1
      rw [Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ d ih =>
    intro e he
    have hex : ∀ k, ∃ i, 0 < e ⟨k, i⟩ := by
      intro k
      by_contra hne
      push_neg at hne
      have h1 := he k
      rw [Finset.sum_eq_zero (fun i _ => Nat.le_zero.1 (hne i))] at h1
      omega
    choose i0 hi0 using hex
    classical
    let e' : (Σ k, ι k) → ℕ := fun p => if p.2 = i0 p.1 then e p - 1 else e p
    have hblk : ∀ k, ∑ i, e' ⟨k, i⟩ = d := by
      intro k
      have h1 := he k
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i0 k))] at h1 ⊢
      have h2 : ∑ i ∈ Finset.univ.erase (i0 k), e' ⟨k, i⟩ = ∑ i ∈ Finset.univ.erase (i0 k), e ⟨k, i⟩ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have := hi0 k
      omega
    obtain ⟨G', hG'deg, hG'⟩ := ih e' hblk
    refine ⟨X i0 * G', ?_, fun z => ?_⟩
    · calc (X i0 * G').totalDegree ≤ (X i0 : MvPolynomial ((k : K) → ι k) ℂ).totalDegree + G'.totalDegree :=
            totalDegree_mul _ _
        _ ≤ 1 + d := by rw [totalDegree_X]; omega
        _ = d + 1 := by ring
    · rw [eval_mul, eval_X, ← hG', segre, Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k)),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k))]
      have h2 : ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e' ⟨k, i⟩ =
          ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e ⟨k, i⟩ := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have h4 : e ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 + 1 := by have := hi0 k; omega
      conv_lhs => rw [h4, pow_succ]
      ring

theorem diag_of_homog (d : ℕ) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blkW ι) f (fun _ => d)) :
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z f = eval (segre z) G := by
  classical
  have hG : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ G : MvPolynomial ((k : K) → ι k) ℂ,
      m ∈ f.support → G.totalDegree ≤ d ∧ ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ m p = eval (segre z) G := by
    intro m
    by_cases hm : m ∈ f.support
    · have hw := hf (mem_support_iff.1 hm)
      obtain ⟨G, h1, h2⟩ := diag_prod d (fun p => m p) (fun k => by
        have := congrFun hw k
        rwa [weight_blkW] at this)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Gf hGf using hG
  refine ⟨∑ m ∈ f.support, C (coeff m f) * Gf m, ?_, fun z => ?_⟩
  · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (hGf m hm).1
  · rw [eval_eq', map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_mul, eval_C, (hGf m hm).2 z]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem comp_mul_homog {σ : Type*} {M : Type*} [AddCancelCommMonoid M] [DecidableEq M] {w : σ → M}
    {ψ : MvPolynomial σ ℂ} {δ : M} (hψ : IsWeightedHomogeneous w ψ δ) (g : MvPolynomial σ ℂ) (n : M) :
    weightedHomogeneousComponent w (n + δ) (g * ψ) = weightedHomogeneousComponent w n g * ψ := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hx
  · refine Finset.sum_congr rfl fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hb : coeff ab.2 ψ = 0
    · simp [hb]
    · have hwb := hψ hb
      have hsum : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w x := by
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← map_add, hab']
      have ha : Finsupp.weight w ab.1 = n := by
        rw [hwb, hx] at hsum
        exact add_right_cancel hsum
      rw [if_pos ha]
  · symm
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with ha
    · by_cases hb : coeff ab.2 ψ = 0
      · simp [hb]
      · exfalso
        apply hx
        have hwb := hψ hb
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← hab', map_add, ha, hwb]
    · simp

end ReciprocityTheory.ChartRestriction.G.Geo
