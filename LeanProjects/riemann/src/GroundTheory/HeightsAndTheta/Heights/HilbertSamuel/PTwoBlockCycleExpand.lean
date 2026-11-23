import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCycleExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockCycleExpand

theorem exists_perm_mem_iff {D : ℕ} (s : Finset (Fin D)) :
    ∃ σ : Equiv.Perm (Fin D), ∀ j, ((σ j : ℕ) < s.card ↔ j ∈ s) := by
  classical
  have hk : s.card ≤ D := by simpa using Finset.card_le_univ s
  have h1 : Fintype.card {j : Fin D // j ∈ s} = Fintype.card {j : Fin D // (j : ℕ) < s.card} := by
    rw [Fintype.card_coe]
    refine (Fintype.card_fin _).symm.trans (Fintype.card_congr ?_)
    exact { toFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, i.2⟩
            invFun := fun j => ⟨j.1, j.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  have h2 : Fintype.card {j : Fin D // ¬ j ∈ s} = Fintype.card {j : Fin D // ¬ (j : ℕ) < s.card} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun j => ?_⟩
  by_cases hj : j ∈ s
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hj,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact iff_of_true (Fintype.equivOfCardEq h1 ⟨j, hj⟩).2 hj
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hj,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact iff_of_false (Fintype.equivOfCardEq h2 ⟨j, hj⟩).2 hj

theorem expand {D : ℕ} (M : MultilinearMap ℤ (fun _ : Fin D => Fin 2 → ℤ) ℤ)
    (hsym : ∀ (v : Fin D → Fin 2 → ℤ) (σ : Equiv.Perm (Fin D)), M (v ∘ σ) = M v) (a b : ℤ) :
    M (fun _ => ![a, b]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℤ) * a ^ i * b ^ (D - i) * M (twoBlockDegList D i) := by
  classical
  have e : (fun _ : Fin D => ![a, b]) =
      (fun _ => a • (Pi.single 0 1 : Fin 2 → ℤ)) + (fun _ => b • (Pi.single 1 1 : Fin 2 → ℤ)) := by
    funext j k
    fin_cases k <;> simp
  have key : ∀ t : Finset (Fin D),
      M (t.piecewise (fun _ => a • (Pi.single 0 1 : Fin 2 → ℤ)) (fun _ => b • (Pi.single 1 1 : Fin 2 → ℤ))) =
        a ^ t.card * b ^ (D - t.card) * M (twoBlockDegList D t.card) := by
    intro t
    obtain ⟨σ, hσ⟩ := exists_perm_mem_iff t
    have hpw : t.piecewise (fun _ => a • (Pi.single 0 1 : Fin 2 → ℤ)) (fun _ => b • (Pi.single 1 1 : Fin 2 → ℤ)) =
        fun j => (if j ∈ t then a else b) • (twoBlockDegList D t.card ∘ σ) j := by
      funext j
      by_cases hj : j ∈ t
      · simp [Finset.piecewise, hj, twoBlockDegList, (hσ j).mpr hj]
      · have : ¬ (σ j : ℕ) < t.card := fun h => hj ((hσ j).mp h)
        simp [Finset.piecewise, hj, twoBlockDegList, this]
    rw [hpw, M.map_smul_univ, hsym, Finset.prod_ite, Finset.prod_const, Finset.prod_const, smul_eq_mul]
    congr 2
    · congr 1
      simp
    · congr 1
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp
  rw [e, M.map_add_univ]
  simp_rw [key]
  rw [← Finset.powerset_univ]
  refine (Finset.sum_powerset_apply_card (fun i => a ^ i * b ^ (D - i) * M (twoBlockDegList D i))
    (x := (Finset.univ : Finset (Fin D)))).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul]
  ring

theorem geoNum_update_last_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {n : ℕ} (v : Fin (n + 1) → K → ℤ) (x y : K → ℤ) :
    geoNum (n + 1) W (Function.update v (Fin.last n) (x + y)) =
      geoNum (n + 1) W (Function.update v (Fin.last n) x) + geoNum (n + 1) W (Function.update v (Fin.last n) y) := by
  simp only [geoNum, Fin.init_update_last, Function.update_self]
  split_ifs
  · simp [add_mul, Finset.sum_add_distrib]
  · simp

theorem geoNum_update_last_smul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {n : ℕ} (v : Fin (n + 1) → K → ℤ) (c : ℤ) (x : K → ℤ) :
    geoNum (n + 1) W (Function.update v (Fin.last n) (c • x)) =
      c * geoNum (n + 1) W (Function.update v (Fin.last n) x) := by
  simp only [geoNum, Fin.init_update_last, Function.update_self]
  split_ifs
  · simp [mul_assoc, Finset.mul_sum]
  · simp

theorem geoNum_update_eq_last {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {n : ℕ} (hsym : ∀ (v : Fin (n + 1) → K → ℤ) (σ : Equiv.Perm (Fin (n + 1))), geoNum (n + 1) W (v ∘ σ) = geoNum (n + 1) W v)
    (v : Fin (n + 1) → K → ℤ) (j : Fin (n + 1)) (z : K → ℤ) :
    geoNum (n + 1) W (Function.update v j z) =
      geoNum (n + 1) W (Function.update (v ∘ Equiv.swap j (Fin.last n)) (Fin.last n) z) := by
  rw [← hsym (Function.update v j z) (Equiv.swap j (Fin.last n)), Function.update_comp_equiv,
    Equiv.symm_swap, Equiv.swap_apply_left]

def geoNumMulti {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (D : ℕ)
    (hsym : ∀ (v : Fin D → K → ℤ) (σ : Equiv.Perm (Fin D)), geoNum D W (v ∘ σ) = geoNum D W v) :
    MultilinearMap ℤ (fun _ : Fin D => K → ℤ) ℤ where
  toFun := geoNum D W
  map_update_add' := by
    intro inst v j x y
    cases D with
    | zero => exact j.elim0
    | succ n =>
      obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
      exact (show geoNum (n + 1) W (Function.update v j (x + y)) =
          geoNum (n + 1) W (Function.update v j x) + geoNum (n + 1) W (Function.update v j y) by
        rw [geoNum_update_eq_last W hsym v j (x + y), geoNum_update_eq_last W hsym v j x,
          geoNum_update_eq_last W hsym v j y, geoNum_update_last_add])
  map_update_smul' := by
    intro inst v j c x
    cases D with
    | zero => exact j.elim0
    | succ n =>
      obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
      exact (show geoNum (n + 1) W (Function.update v j (c • x)) = c • geoNum (n + 1) W (Function.update v j x) by
        rw [geoNum_update_eq_last W hsym v j (c • x), geoNum_update_eq_last W hsym v j x,
          geoNum_update_last_smul, smul_eq_mul])

variable {κ : Type} [Fintype κ]

theorem geoNum_comp_perm {P W : Ideal (MRing (FinTwoTypeFamily κ))} {D : ℕ} (hP : IsArithVar P (D + 1)) {s : MRing (FinTwoTypeFamily κ)}
    {α : Fin 2 → ℕ} (hs : IsMultiHomog s α) (hW : W ∈ divSupp P s) (hv : ¬ IsHorizontal W)
    (v : Fin D → Fin 2 → ℤ) (σ : Equiv.Perm (Fin D)) : geoNum D W (v ∘ σ) = geoNum D W v := by
  have hPp : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hsP : s ∉ P := by
    intro hsP
    have h1 := hW.1
    rw [sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsP), Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff] at h1
    exact hv (h1 ▸ hP.2.2.1)
  have hdim : ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) = ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞) := by
    have h := dim_quot_minimal_add_one P W s hsP hW.1
    rw [hP.2.2.2] at h
    refine ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one (h.trans ?_)
    congr 1
  have hMP : IsMultiProjPrime W := ⟨hWp, isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1.2.1 hs hW.1, hW.2⟩
  have : Fact (charOf W).Prime := ⟨charOf_prime hWp hv⟩
  rw [← Bridge.intNum_map_eq_geoNum (charOf W) D W hMP (Inter.C_charOf_mem W) hdim,
    ← Bridge.intNum_map_eq_geoNum (charOf W) D W hMP (Inter.C_charOf_mem W) hdim,
    MixedNumberPolynomial.intNum_perm]

theorem vertCycleNum_expand {P : Ideal (MRing (FinTwoTypeFamily κ))} {D : ℕ} (hP : IsArithVar P (D + 1)) {s : MRing (FinTwoTypeFamily κ)}
    {α : Fin 2 → ℕ} (hs : IsMultiHomog s α) (a b : ℕ) :
    vertCycleNum P s (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        vertCycleNum P s (twoBlockDegList D i) := by
  classical
  have hfin := divSupp_finite P s
  unfold vertCycleNum
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [Set.Finite.mem_toFinset] at hW
  split_ifs with hh
  · simp
  · have h := expand (geoNumMulti W D fun v σ => geoNum_comp_perm hP hs hW hh v σ)
      (fun v σ => geoNum_comp_perm hP hs hW hh v σ) (a : ℤ) (b : ℤ)
    change geoNum D W _ = ∑ i ∈ Finset.range (D + 1), _ * geoNum D W _ at h
    rw [h]
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem isMultiHomog_twoBlockDen (c : κ) :
    IsMultiHomog (twoBlockDen c) (fun k => ∑ i, (Finsupp.single (⟨0, c⟩ : Σ k, FinTwoTypeFamily κ k) 1) ⟨k, i⟩) :=
  isMultiHomog_X _

theorem isMultiHomog_twoBlockNum (l : Ix κ → ℤ) :
    IsMultiHomog (twoBlockNum l) (fun k : Fin 2 => if k = 1 then 1 else 0) := by
  classical
  intro m hm k
  unfold twoBlockNum at hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hm
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at hj
  have hm' : Finsupp.single (⟨1, j.2⟩ : Σ k, FinTwoTypeFamily κ k) 1 = m := by
    by_contra h
    simp [h] at hj
  subst hm'
  fin_cases k <;> simp [Finsupp.single_apply]

end TwoBlockCycleExpand

open TwoBlockCycleExpand in

theorem TwoBlockCycleExpand.proof : TwoBlockCycleExpand.Statement := by
  classical
  have hA := CoordArithOfFnField.proof
  have hF := TwoBlockFnField.proof
  intro D Ω _ _ κ _ x B c l hx _ hB _ _ a b
  obtain ⟨hFp, -⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx
  obtain ⟨i, hi⟩ := hx.2.1.2.2 ()
  have hx0 : x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff x _).mpr (by rw [h]; rfl))
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  unfold twoBlockVert
  rw [vertCycleNum_expand hpA (isMultiHomog_twoBlockNum l) a b,
    vertCycleNum_expand hpA (isMultiHomog_twoBlockDen c) a b, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
