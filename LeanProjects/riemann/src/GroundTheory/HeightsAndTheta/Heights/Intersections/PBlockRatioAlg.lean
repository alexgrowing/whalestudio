import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalImageZ
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockRatioAlgebraic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem mCoordIdeal_comp_v {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (y' : (Σ k', ι' k') → Ω) : mCoordIdeal (fun p ↦ y' (v p)) = imageZ v (mCoordIdeal y') := by
  have e : ∀ f : MRing ι, mConeMap y' (rename v f) = rename κ (mConeMap (fun p ↦ y' (v p)) f) := by
    intro f
    have h : ((mConeMap y').comp (rename v) : MRing ι →ₐ[ℤ] MvPolynomial K' Ω) =
        ((rename κ).restrictScalars ℤ).comp (mConeMap fun p ↦ y' (v p)) := by
      refine MvPolynomial.algHom_ext fun p ↦ ?_
      simp [mConeMap, hv.2.2.1 p]
    exact congrArg (fun φ : MRing ι →ₐ[ℤ] MvPolynomial K' Ω ↦ φ f) h
  ext f
  change _ ↔ rename v f ∈ mCoordIdeal y'
  simp only [mCoordIdeal, RingHom.mem_ker, e]
  exact (map_eq_zero_iff _ (rename_injective κ hv.1)).symm

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem algebraMap_int_injective (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) :
    Function.Injective (algebraMap ℤ Ω) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hm : a ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply, ha, C_0]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h] at hm
  exact (Submodule.mem_bot ℤ).mp hm

omit [Fintype K] in

theorem isMultiHomog_C (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst this
  simp

def homogN (c : ∀ k, ι k) (N : ℕ) (f : MRing ι) : MRing ι :=
  ∑ m ∈ f.support, C (coeff m f) * ∏ p : Σ k, ι k, X p ^ m p * X ⟨p.1, c p.1⟩ ^ (N - m p)

theorem isMultiHomog_homogN [DecidableEq K] (c : ∀ k, ι k) (N : ℕ) (f : MRing ι)
    (hN : f.totalDegree ≤ N) :
    IsMultiHomog (homogN c N f) (∑ p : Σ k, ι k, N • (Pi.single p.1 1 : K → ℕ)) := by
  refine AvoidRing.isMultiHomog_sum _ _ fun m hm ↦ ?_
  have hle : ∀ p, m p ≤ N := fun p ↦
    ((monomial_le_degreeOf p hm).trans (degreeOf_le_totalDegree f p)).trans hN
  have h := AvoidRing.isMultiHomog_mul (isMultiHomog_C (ι := ι) (coeff m f))
    (AvoidRing.isMultiHomog_prod Finset.univ
      (fun p : Σ k, ι k ↦ (X p : MRing ι) ^ m p * X ⟨p.1, c p.1⟩ ^ (N - m p))
      (fun p ↦ N • (Pi.single p.1 1 : K → ℕ)) fun p _ ↦ by
        have h1 := AvoidRing.isMultiHomog_mul
          (AvoidRing.isMultiHomog_pow (AvoidRing.isMultiHomog_X (R := ℤ) (ι := ι) p.1 p.2) (m p))
          (AvoidRing.isMultiHomog_pow (AvoidRing.isMultiHomog_X (R := ℤ) (ι := ι) p.1 (c p.1)) (N - m p))
        rwa [← add_smul, Nat.add_sub_cancel' (hle p)] at h1)
  rwa [zero_add] at h

theorem aeval_homogN {F : Type} [Field F] (c : ∀ k, ι k) (N : ℕ) (f : MRing ι)
    (hN : f.totalDegree ≤ N) (w : (Σ k, ι k) → F) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    aeval w (homogN c N f) = (∏ p : Σ k, ι k, w ⟨p.1, c p.1⟩) ^ N *
      aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) f := by
  classical
  have hsum : aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) f =
      ∑ m ∈ f.support, aeval (fun p ↦ w p / w ⟨p.1, c p.1⟩) (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [hsum, Finset.mul_sum, homogN, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle : ∀ p, m p ≤ N := fun p ↦
    ((monomial_le_degreeOf p hm).trans (degreeOf_le_totalDegree f p)).trans hN
  rw [map_mul, aeval_C, map_prod, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← Finset.prod_pow, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hle p)
  rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, div_pow, he, Nat.add_sub_cancel_left, pow_add]
  rw [mul_comm (w ⟨p.1, c p.1⟩ ^ m p), mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ (hw p.1)),
    mul_comm]

end BlockRatioAlgebraic

open BlockRatioAlgebraic CoordinateConeArithVar in

theorem BlockRatioAlg.proof : BlockRatioAlg.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hv hP' hP q c hqc hc
  obtain ⟨Ω, _, y', hy', hbir⟩ := HilbertSamuel.BirationalModelExists.proof K' ι' P' (n + 1) hP'

  choose c' hc' using hP'.2.1.2.2
  have hy'c : ∀ k', y' ⟨k', c' k'⟩ ≠ 0 := fun k' h0 ↦ hc' k' (by
    rw [← hy', mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨_, ⟨hprime', -, -⟩, hhor', hdim'⟩ := hP'
  have hZ : Function.Injective (algebraMap ℤ Ω) := algebraMap_int_injective y' (hy' ▸ hhor')

  have hΩ : Algebra.trdeg ℤ Ω = n := by
    have htr := ConeTrdeg.proof K' ι' Ω y' hbir (fun k ↦ ⟨c' k, hy'c k⟩) (hy' ▸ hhor')
    rw [hy'] at htr
    have := hprime'
    have hA := IntDomainDim.proof (MRing ι' ⧸ P') (CoordinateConeArithVar.algebraMap_injective P' hhor')
    rw [hdim', htr, map_add, map_natCast] at hA
    have hA' : ((n + 1 + Fintype.card K' : ℕ) : ℕ∞) =
        Cardinal.toENat (Algebra.trdeg ℤ Ω) + Fintype.card K' + 1 := by exact_mod_cast hA
    obtain ⟨t, ht⟩ : ∃ t : ℕ, Cardinal.toENat (Algebra.trdeg ℤ Ω) = t := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at hA'
      simp at hA'
    rw [ht] at hA'
    have : n + 1 + Fintype.card K' = t + Fintype.card K' + 1 := by exact_mod_cast hA'
    rw [Cardinal.toENat_eq_natCast] at ht
    rw [ht]
    congr 1
    omega

  set y : (Σ k, ι k) → Ω := fun p ↦ y' (v p) with hydef
  have hyP : mCoordIdeal y = imageZ v P' := by rw [← hy']; exact mCoordIdeal_comp_v hv y'
  choose c0 hc0 using hP.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k h0 ↦ hc0 k (by
    rw [← hyP, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  set A : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range (ratioPt y c0)) with hAdef
  have hZA : Function.Injective (algebraMap ℤ A) := fun a b h ↦ hZ (congrArg Subtype.val h)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective ℤ A).mpr hZA
  have : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).mpr Subtype.val_injective
  have : FaithfulSMul A (MvPolynomial K A) :=
    (faithfulSMul_iff_algebraMap_injective A (MvPolynomial K A)).mpr (C_injective _ _)

  let Ψ : MRing ι →ₐ[ℤ] MvPolynomial K A :=
    aeval fun p ↦ C ⟨ratioPt y c0 p, Algebra.subset_adjoin ⟨p, rfl⟩⟩ * X p.1
  have hΨ : ∀ f, MvPolynomial.map (algebraMap A Ω) (Ψ f) = mConeMap (ratioPt y c0) f := by
    intro f
    have e : ((MvPolynomial.map (algebraMap A Ω)).comp (Ψ : MRing ι →+* MvPolynomial K A)) =
        (mConeMap (ratioPt y c0) : MRing ι →+* MvPolynomial K Ω) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun p ↦ ?_)
      · simp [Ψ, mConeMap]
      · simp [Ψ, mConeMap]
    exact RingHom.congr_fun e f
  have hker : RingHom.ker Ψ = imageZ v P' := by
    ext f
    rw [RingHom.mem_ker, ← hyP, mCoordIdeal_ratioPt y c0 hy0, mCoordIdeal, RingHom.mem_ker, ← hΨ]
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ Subtype.val_injective)).symm
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hP
  rw [← hker] at hprime hhor hdim
  have := hprime
  have hB := IntDomainDim.proof (MRing ι ⧸ RingHom.ker Ψ)
    (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hdim] at hB
  have hB' : Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ RingHom.ker Ψ)) = (n + Fintype.card K : ℕ) := by
    have : ((n + 1 + Fintype.card K : ℕ) : ℕ∞) =
        Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ RingHom.ker Ψ)) + 1 := by exact_mod_cast hB
    obtain ⟨t, ht⟩ : ∃ t : ℕ, Cardinal.toENat (Algebra.trdeg ℤ (MRing ι ⧸ RingHom.ker Ψ)) = t := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at this
      simp at this
    rw [ht] at this ⊢
    have : n + 1 + Fintype.card K = t + 1 := by exact_mod_cast this
    congr 1
    omega
  rw [Cardinal.toENat_eq_natCast] at hB'
  have hle : Algebra.trdeg ℤ (MRing ι ⧸ RingHom.ker Ψ) ≤ Algebra.trdeg ℤ (MvPolynomial K A) :=
    trdeg_le_of_injective (Ideal.kerLiftAlg Ψ) (Ideal.kerLiftAlg_injective Ψ)
  rw [← trdeg_add_eq ℤ A (A := MvPolynomial K A), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
    Cardinal.mk_fintype, hB'] at hle

  have hsum := trdeg_add_eq ℤ A (A := Ω)
  rw [hΩ] at hsum
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.1
    ((le_self_add.trans hsum.le).trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.1
    ((le_add_self.trans hsum.le).trans_lt (Cardinal.natCast_lt_aleph0 (n := n)))
  rw [ha, hb] at hsum
  rw [ha] at hle
  have h1 : a + b = n := by exact_mod_cast hsum
  have h2 : n + Fintype.card K ≤ a + Fintype.card K := by exact_mod_cast hle
  have hb0 : Algebra.trdeg A Ω = 0 := by rw [hb]; norm_cast; omega
  have : Algebra.IsAlgebraic A Ω := trdeg_eq_zero_iff.mp hb0

  have hyc : y' c ≠ 0 := fun h0 ↦ hc (by
    rw [← hy', mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨p, hp0, hpr⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) (y' q / y' c)
  have hF : ∀ j : ℕ, ∃ F : MRing ι, aeval (ratioPt y c0) F = (p.coeff j : Ω) := by
    intro j
    have hmem : (p.coeff j : Ω) ∈ Algebra.adjoin ℤ (Set.range (ratioPt y c0)) := (p.coeff j).2
    rw [Algebra.adjoin_range_eq_range_aeval] at hmem
    obtain ⟨F, hF⟩ := hmem
    exact ⟨F, hF⟩
  choose F hF using hF
  set m := p.natDegree with hm
  set N := ∑ j ∈ Finset.range (m + 1), (F j).totalDegree with hN
  have hNle : ∀ j : Fin (m + 1), (F j).totalDegree ≤ N := fun j ↦
    Finset.single_le_sum (f := fun j ↦ (F j).totalDegree) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 j.2)
  set D := (∏ p : Σ k, ι k, y ⟨p.1, c0 p.1⟩) ^ N with hD
  have hD0 : D ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun p _ ↦ hy0 p.1)
  have hval : ∀ j : Fin (m + 1), aeval y (homogN c0 N (F j)) = D * (p.coeff j : Ω) := by
    intro j
    rw [aeval_homogN c0 N (F j) (hNle j) y hy0, ← hF]
    rfl
  have hdeg := fun j : Fin (m + 1) ↦ isMultiHomog_homogN c0 N (F j) (hNle j)
  refine ⟨m, fun j ↦ homogN c0 N (F j), _, hdeg, ?_, ?_⟩
  ·
    rw [← hyP]
    intro hmem
    rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y (hdeg _)] at hmem
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ (∑ p : Σ k, ι k, N • (Pi.single p.1 1 : K → ℕ)) k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (X_ne_zero k)
    have h0 := (mul_eq_zero.1 hmem).resolve_right hX
    rw [C_eq_zero, hval] at h0
    have hlc : (p.coeff m : Ω) ≠ 0 := fun h ↦
      (Polynomial.leadingCoeff_ne_zero.2 hp0) (Subtype.ext h)
    exact mul_ne_zero hD0 hlc h0
  ·
    have hG : IsMultiHomog (∑ j : Fin (m + 1), rename v (homogN c0 N (F j)) * X q ^ (j : ℕ) *
        X c ^ (m - j : ℕ)) (Function.extend κ (∑ p : Σ k, ι k, N • (Pi.single p.1 1 : K → ℕ)) 0 +
          m • (Pi.single q.1 1 : K' → ℕ)) := by
      refine AvoidRing.isMultiHomog_sum _ _ fun j _ ↦ ?_
      have h1 := AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_mul
        (ArithmeticIntersectionHorizontal.isMultiHomog_rename hv (hdeg j))
        (AvoidRing.isMultiHomog_pow (AvoidRing.isMultiHomog_X (R := ℤ) (ι := ι') q.1 q.2) (j : ℕ)))
        (AvoidRing.isMultiHomog_pow (AvoidRing.isMultiHomog_X (R := ℤ) (ι := ι') c.1 c.2) (m - j : ℕ))
      rw [show (Pi.single c.1 1 : K' → ℕ) = Pi.single q.1 1 by rw [hqc]] at h1
      rwa [add_assoc, ← add_smul, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 j.2)] at h1
    rw [← hy', mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y' hG]
    suffices h : aeval y' (∑ j : Fin (m + 1), rename v (homogN c0 N (F j)) * X q ^ (j : ℕ) *
        X c ^ (m - j : ℕ)) = 0 by rw [h, C_0, zero_mul]
    have hpr' : ∑ j ∈ Finset.range (m + 1), (p.coeff j : Ω) * (y' q / y' c) ^ j = 0 := by
      rw [← hpr, Polynomial.aeval_eq_sum_range]
      rfl
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (p.coeff j : Ω) * (y' q / y' c) ^ j)] at hpr'
    have e : ∀ j : Fin (m + 1), aeval y' (rename v (homogN c0 N (F j)) * X q ^ (j : ℕ) * X c ^ (m - j : ℕ)) =
        D * y' c ^ m * ((p.coeff j : Ω) * (y' q / y' c) ^ (j : ℕ)) := by
      intro j
      have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.2
      rw [map_mul, map_mul, map_pow, map_pow, aeval_X, aeval_X, aeval_rename]
      have hv' : aeval (y' ∘ v) (homogN c0 N (F j)) = D * (p.coeff j : Ω) := hval j
      rw [hv', div_pow, show y' c ^ m = y' c ^ (j : ℕ) * y' c ^ (m - j : ℕ) by
        rw [← pow_add, Nat.add_sub_cancel' hj]]
      field_simp
    rw [map_sum, Finset.sum_congr rfl fun j _ ↦ e j, ← Finset.mul_sum, hpr', mul_zero]

end GroundTheory.Heights₂.Heights.Inter
