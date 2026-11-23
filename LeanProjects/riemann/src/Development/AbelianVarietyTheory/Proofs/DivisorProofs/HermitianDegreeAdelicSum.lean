import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticeContainsScaledBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledStandardLatticePadicSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticePrimeToPBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatLogEqLogStatement

set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead
open scoped ComplexOrder

namespace GlobalTheory.LieRead

theorem det_cols_ne_zero_of_linearIndependent {K : Type} [Field K] {g : ℕ} (x : Fin g → Fin g → K) (hx : LinearIndependent K x) :
    (Matrix.of fun i k => x k i).det ≠ 0 := by
  have h1 : IsUnit (Matrix.of x) := (Matrix.linearIndependent_rows_iff_isUnit).mp hx
  have h2 : (Matrix.of fun i k => x k i) = (Matrix.of x).transpose := rfl
  rw [h2, Matrix.det_transpose]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h1).ne_zero

theorem finsum_lnGrP_eq_add_padicValNat_relIndex : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime]
    (L L' : Submodule (𝓞 K) (Fin g → K)), Full L → Full L' → L ≤ L' →
    ∑ᶠ j : K →+* ℂ_[p], ∑ k : Fin g, lnGrP p j L k =
      ∑ᶠ j : K →+* ℂ_[p], ∑ k : Fin g, lnGrP p j L' k +
        (padicValNat p (L.toAddSubgroup.relIndex L'.toAddSubgroup) : ℝ) * Real.log p := by
  intro K _ _ g p _ L L' hL hL' hle
  obtain ⟨x, s, hx1, hx2, hx3, hx4⟩ := GlobalTheory.T.full_lattice_prime_to_p_basis K g p L hL
  obtain ⟨x', s', hx1', hx2', hx3', hx4'⟩ := GlobalTheory.T.full_lattice_prime_to_p_basis K g p L' hL'
  have e1 : ∑ᶠ j : K →+* ℂ_[p], ∑ k : Fin g, lnGrP p j L k =
      (padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x k i).det) : ℝ) * Real.log p := by
    rw [finsum_congr fun j => GlobalTheory.T.lattice_padic_grading_det K g p j L x s hx1 hx2 hx3 hx4, finsum_neg_distrib,
      GlobalTheory.T.p_adic_product_formula K p _ (det_cols_ne_zero_of_linearIndependent x hx2), neg_neg]
  have e2 : ∑ᶠ j : K →+* ℂ_[p], ∑ k : Fin g, lnGrP p j L' k =
      (padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x' k i).det) : ℝ) * Real.log p := by
    rw [finsum_congr fun j => GlobalTheory.T.lattice_padic_grading_det K g p j L' x' s' hx1' hx2' hx3' hx4', finsum_neg_distrib,
      GlobalTheory.T.p_adic_product_formula K p _ (det_cols_ne_zero_of_linearIndependent x' hx2'), neg_neg]
  have e3 := GlobalTheory.T.lattice_padic_grading_compare K g p L L' x x' s s' hL hL' hle hx1 hx2 hx3 hx4 hx1' hx2' hx3' hx4'
  have e4 : (padicValNat p (L.toAddSubgroup.relIndex L'.toAddSubgroup) : ℝ) =
      (padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x k i).det) : ℝ) -
        (padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x' k i).det) : ℝ) := by
    have e5 := congrArg (fun z : ℤ => (z : ℝ)) e3
    simp only [Int.cast_sub, Int.cast_natCast] at e5
    exact e5
  rw [e1, e2, e4]
  ring

theorem HermFam.form_smul_left' {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (a : K) (x y : V) : h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm σ y (a • x), h.smul_right, map_mul, h.conj_symm]

theorem HermFam.gram_natCast_smul_single {K : Type} [Field K] {g : ℕ} (h : HermFam K (Fin g → K)) (σ : K →+* ℂ) (D : ℕ) :
    h.gram σ (fun k => (D : K) • (Pi.single k 1 : Fin g → K)) =
      ((D : ℂ) ^ 2) • h.gram σ (fun k => (Pi.single k 1 : Fin g → K)) := by
  ext i j
  simp only [HermFam.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, HermFam.form_smul_left', h.smul_right,
    map_natCast, Complex.conj_natCast]
  ring

theorem HermFam.log_det_gram_natCast_smul_single {K : Type} [Field K] {g : ℕ} (h : HermFam K (Fin g → K)) (σ : K →+* ℂ) (D : ℕ)
    (hD : 0 < D) :
    Real.log (h.gram σ (fun k => (D : K) • (Pi.single k 1 : Fin g → K))).det.re =
      2 * g * Real.log D + Real.log (h.gram σ (fun k => (Pi.single k 1 : Fin g → K))).det.re := by
  have hli : LinearIndependent K (fun k : Fin g => (Pi.single k 1 : Fin g → K)) := by
    have := (Pi.basisFun K (Fin g)).linearIndependent
    convert this using 1
    funext k
    simp
  have hpos : 0 < (h.gram σ (fun k => (Pi.single k 1 : Fin g → K))).det :=
    (h.posDef σ g _ hli).det_pos
  have hre : 0 < (h.gram σ (fun k => (Pi.single k 1 : Fin g → K))).det.re := (Complex.pos_iff.mp hpos).1
  rw [HermFam.gram_natCast_smul_single, Matrix.det_smul, Fintype.card_fin]
  have hc : ((D : ℂ) ^ 2) ^ g = (((D : ℝ) ^ 2) ^ g : ℝ) := by push_cast; ring
  rw [hc, Complex.re_ofReal_mul, Real.log_mul (by positivity) hre.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem deg_eq_neg_adelSum_div_finrank : ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (L : Submodule (𝓞 K) (Fin g → K))
    (h : HermFam K (Fin g → K)), Full L → deg h L = -(adelSum h L) / Module.finrank ℚ K := by
  intro K _ _ g L h hL
  obtain ⟨D, hD, hDL⟩ := GlobalTheory.T.full_lattice_contains_scaled_basis K g L hL
  set w : Fin g → Fin g → K := fun k => (D : K) • (Pi.single k 1 : Fin g → K) with hw_def
  have hDK : (D : K) ≠ 0 := by exact_mod_cast hD.ne'
  have htop : Submodule.span K (Set.range w) = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun v => ?_
    have hv : v = ∑ k, (v k / D) • w k := by
      funext i
      simp [w, Finset.sum_apply, Pi.single_apply, hDK]
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hwli : LinearIndependent K w := by
    have h0 : LinearIndependent K (fun k : Fin g => (Pi.single k 1 : Fin g → K)) := by
      have := (Pi.basisFun K (Fin g)).linearIndependent
      convert this using 1
      funext k
      simp
    have := h0.units_smul (fun _ => Units.mk0 (D : K) hDK)
    convert this using 1
    funext k
    simp [w, Units.smul_def]
  have hw : IsFrame K L w := ⟨hDL, hwli, fun x _ => htop ▸ Submodule.mem_top⟩
  set Dst := Submodule.span (𝓞 K) (Set.range w) with hDst
  have hDstL : Dst ≤ L := Submodule.span_le.mpr (Set.range_subset_iff.mpr hDL)
  have hDstF : Full Dst := by
    refine ⟨Submodule.fg_span (Set.finite_range w), ?_⟩
    rw [hDst, Submodule.span_span_of_tower, htop]
  set I := Dst.toAddSubgroup.relIndex L.toAddSubgroup with hI
  have hI0 : I ≠ 0 := hw.relIndex_ne_zero hL.1
  have hloc : ∀ p : ℕ, (if hp : p.Prime then (haveI : Fact p.Prime := ⟨hp⟩;
      ∑ᶠ j : K →+* ℂ_[p], ∑ k, lnGrP p j L k) else 0) =
      (g * Module.finrank ℚ K : ℝ) * (if p.Prime then (padicValNat p D : ℝ) * Real.log p else 0) -
        (if p.Prime then (padicValNat p I : ℝ) * Real.log p else 0) := by
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [dif_pos hp, if_pos hp, if_pos hp]
      have e1 := finsum_lnGrP_eq_add_padicValNat_relIndex K g p Dst L hDstF hL hDstL
      have e2 := GlobalTheory.T.scaled_standard_lattice_padic_sum K g p D hD
      rw [← hI] at e1
      change ∑ᶠ j : K →+* ℂ_[p], ∑ k, lnGrP p j Dst k = _ at e2
      linarith
    · rw [dif_neg hp, if_neg hp, if_neg hp]
      ring
  have hfin : finPart L = g * Module.finrank ℚ K * Real.log D - Real.log I := by
    unfold finPart
    obtain ⟨sD, vD⟩ := GlobalTheory.T.sum_padicValNat_log_eq_log D hD.ne'
    obtain ⟨sI, vI⟩ := GlobalTheory.T.sum_padicValNat_log_eq_log I hI0
    rw [finsum_congr hloc, finsum_sub_distrib (sD.subset (Function.support_mul_subset_right _ _)) sI,
      ← mul_finsum _ _, vD, vI]
  rw [arakelovDegree_eq_degreeOfFamily h hL.1 hw]
  unfold degreeOfFamily adelSum
  rw [hfin]
  have hg : ∀ σ : K →+* ℂ, Real.log (h.gram σ w).det.re =
      2 * g * Real.log D + Real.log (h.gram σ (fun k => (Pi.single k 1 : Fin g → K))).det.re :=
    fun σ => HermFam.log_det_gram_natCast_smul_single h σ D hD
  rw [Finset.sum_congr rfl fun σ _ => hg σ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card K ℂ]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp
  simp only [nsmul_eq_mul]
  ring

end GlobalTheory.LieRead
