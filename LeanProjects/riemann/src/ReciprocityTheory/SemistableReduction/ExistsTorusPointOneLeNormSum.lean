import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable abbrev unitBallRing (K : Type*) [NormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

theorem mem_unitBallRing {K : Type*} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ unitBallRing K ↔ ‖x‖ ≤ 1 := by
  first
  | (change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
     rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one])
  | (rw [unitBallRing, Valuation.mem_valuationSubring_iff]
     simp [NormedField.valuation_apply, ← NNReal.coe_le_coe])

theorem residue_eq_zero_iff_norm_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : unitBallRing K) :
    IsLocalRing.residue (unitBallRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx1 : ‖(x : K)‖ ≤ 1 := (mem_unitBallRing (x : K)).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx1 fun h1 => hnu ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : K)⁻¹ ∈ unitBallRing K := by
      rw [mem_unitBallRing, norm_inv, h1, inv_one]
    have hm : x * ⟨(x : K)⁻¹, hinv⟩ = 1 := Subtype.ext (by simp [hx0])
    exact ⟨⟨x, ⟨(x : K)⁻¹, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h := congrArg (fun t : unitBallRing K => ‖(t : K)‖) hy
    first
    | simp only [MulMemClass.coe_mul, OneMemClass.coe_one, norm_mul, norm_one] at h
    | simp at h
    have hy1 : ‖(y : K)‖ ≤ 1 := (mem_unitBallRing (y : K)).1 y.2
    nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]

theorem infinite_residues {K : Type*} [NormedField K] [IsUltrametricDist K] (K₀ : Subfield K)
    (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) :
    {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}.Infinite := by
  classical
  intro hfin
  have hrep : ∀ y ∈ {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y},
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y :=
    fun y hy => hy
  choose! r hr using hrep
  unfold ResidueFieldInfiniteOn at hK₀
  obtain ⟨x, hxK, hx1, hxs⟩ := hK₀ (insert 0 (hfin.toFinset.image fun y => (r y : K)))
  have hx0 : 1 ≤ ‖x‖ := by simpa using hxs 0 (Finset.mem_insert_self _ _)
  have hxn : ‖x‖ = 1 := le_antisymm hx1 hx0
  let xb : unitBallRing K := ⟨x, (mem_unitBallRing x).2 hx1⟩
  have hmem : IsLocalRing.residue _ xb ∈ {y : IsLocalRing.ResidueField (unitBallRing K) |
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y} :=
    ⟨xb, hxK, hxn, rfl⟩
  obtain ⟨-, -, hreq⟩ := hr _ hmem
  have h0 : IsLocalRing.residue _ (xb - r (IsLocalRing.residue _ xb)) = 0 := by
    rw [map_sub, hreq, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at h0
  have h0' : ‖x - (r (IsLocalRing.residue _ xb) : K)‖ < 1 := by simpa [xb] using h0
  have h1 := hxs (r (IsLocalRing.residue _ xb) : K)
    (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 hmem, rfl⟩))
  linarith

theorem exists_torus_point_one_le_norm_sum {K : Type*} [NormedField K] [IsUltrametricDist K]
    (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) {n : ℕ}
    (F : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → K) (ha : ∀ χ, ‖a χ‖ ≤ 1)
    (χ₀ : Fin n → ℤ) (hχ₀ : χ₀ ∈ F) (ha₀ : ‖a χ₀‖ = 1) :
    ∃ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) ∧
      1 ≤ ‖∑ χ ∈ F, a χ * ∏ i, τ i ^ χ i‖ := by
  classical
  let N : ℕ := ∑ χ ∈ F, ∑ i, (χ i).natAbs
  have hN : ∀ χ ∈ F, ∀ i, 0 ≤ χ i + N := by
    intro χ hχ i
    have h1 : (χ i).natAbs ≤ ∑ j, (χ j).natAbs :=
      Finset.single_le_sum (f := fun j => (χ j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j, (χ j).natAbs ≤ N :=
      Finset.single_le_sum (f := fun χ : Fin n → ℤ => ∑ j, (χ j).natAbs)
        (fun _ _ => Nat.zero_le _) hχ
    omega
  let e : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun χ =>
    Finsupp.equivFunOnFinite.symm (fun i => (χ i + N).toNat)
  have he : ∀ χ ∈ F, ∀ χ' ∈ F, e χ = e χ' → χ = χ' := by
    intro χ hχ χ' hχ' h
    funext i
    have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h3
    have h1 := hN χ hχ i
    have h2 := hN χ' hχ' i
    omega
  let aO : (Fin n → ℤ) → unitBallRing K := fun χ => ⟨a χ, (mem_unitBallRing _).2 (ha χ)⟩
  let P : MvPolynomial (Fin n) (unitBallRing K) := ∑ χ ∈ F, monomial (e χ) (aO χ)
  have hcoeff : coeff (e χ₀) P = aO χ₀ := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem χ₀ hχ₀]
    · simp
    · intro χ hχ hne
      rw [if_neg]
      exact fun h => hne (he χ hχ χ₀ hχ₀ h)
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P ≠ 0 := by
    intro h0
    have h4 := congrArg (coeff (e χ₀)) h0
    rw [coeff_map, hcoeff, coeff_zero, residue_eq_zero_iff_norm_lt_one] at h4
    exact absurd ha₀ (ne_of_lt h4)
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Set.pi Set.univ (fun _ : Fin n =>
      {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
        (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}),
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (funext_set _ (fun _ => infinite_residues K₀ hK₀) (fun x hx => by
      rw [hcon x hx, map_zero]))
  choose σ hσK hσ1 hσr using fun i => hy i (Set.mem_univ i)
  refine ⟨fun i => (σ i : K), fun i => ⟨hσK i, hσ1 i⟩, ?_⟩
  have hr : IsLocalRing.residue (unitBallRing K) (eval σ P) ≠ 0 := by
    have hy' : y = fun i => IsLocalRing.residue (unitBallRing K) (σ i) :=
      funext fun i => (hσr i).symm
    have h5 : eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) =
        IsLocalRing.residue (unitBallRing K) (eval σ P) := by
      rw [eval_map, hy', MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hom_eval₂,
        RingHom.comp_id]
    rwa [h5] at hyne
  have hge : 1 ≤ ‖((eval σ P : unitBallRing K) : K)‖ :=
    not_lt.1 fun h => hr ((residue_eq_zero_iff_norm_lt_one _).2 h)
  have hσ0 : ∀ i, (σ i : K) ≠ 0 := fun i h => by
    have h6 := hσ1 i
    rw [h, norm_zero] at h6
    exact zero_ne_one h6
  have hval : ((eval σ P : unitBallRing K) : K) =
      ∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ (χ i + N).toNat := by
    simp only [P, map_sum, eval_monomial]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp [e, aO]
  have hterm : ∀ χ ∈ F, ∏ i, (σ i : K) ^ (χ i + N).toNat =
      (∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    intro χ hχ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN χ hχ i), zpow_add₀ (hσ0 i), zpow_natCast]
  have hsum : ((eval σ P : unitBallRing K) : K) =
      (∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hterm χ hχ, mul_assoc]
  have hnorm1 : ‖∏ i, (σ i : K) ^ N‖ = 1 := by
    rw [norm_prod]
    simp [norm_pow, hσ1]
  rw [hsum, norm_mul, hnorm1, mul_one] at hge
  exact hge

end ReciprocityTheory.MultiplicativeHeights
