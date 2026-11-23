import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar

noncomputable section
namespace GlobalTheory.CartanInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

variable {p q : ℕ}

def l1 {n : Type} [Fintype n] (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

def Kc (p q : ℕ) : Set (UpqT p q) := {k | IsKC (UpqT.mat k)}

def eP (B : Fin p → Fin q → ℂ) : UpqT p q :=
  GlobalTheory.CompactDualExists.expU ⟨pY B, (pY_mem B).1⟩

theorem mat_eP (B : Fin p → Fin q → ℂ) : UpqT.mat (eP B) = NormedSpace.exp (pY B) := rfl

theorem continuous_eP : Continuous (eP : (Fin p → Fin q → ℂ) → UpqT p q) :=
  GlobalTheory.CompactDualExists.continuous_expU.comp (continuous_pY.subtype_mk _)

theorem mat_mul (x y : UpqT p q) : UpqT.mat (x * y) = UpqT.mat x * UpqT.mat y := rfl

theorem mat_one : UpqT.mat (1 : UpqT p q) = 1 := rfl

theorem isKC_fromBlocks (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ) :
    IsKC (Matrix.fromBlocks U 0 0 V : Mat p q) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

theorem mem_Kc_iff (k : UpqT p q) : k ∈ Kc p q ↔
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      UpqT.mat k = Matrix.fromBlocks U 0 0 V := by
  constructor
  · intro hk
    have hk' : IsKC (UpqT.mat k) := hk
    have h : UpqT.mat k = Matrix.fromBlocks (UpqT.mat k).toBlocks₁₁ 0 0 (UpqT.mat k).toBlocks₂₂ := by
      ext a b
      rcases a with i | i <;> rcases b with j | j
      · rfl
      · exact hk' _ _ (by simp [sameBlock])
      · exact hk' _ _ (by simp [sameBlock])
      · rfl
    have hJ := GlobalTheory.UpqTopology.mat_unitary k
    rw [h] at hJ
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj] at hJ
    refine ⟨_, ?_, _, ?_, h⟩
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.1
    · rw [Matrix.mem_unitaryGroup_iff']; simpa [star_eq_conjTranspose] using hJ.2.2.2
  · rintro ⟨U, -, V, -, h⟩
    show IsKC (UpqT.mat k)
    rw [h]; exact isKC_fromBlocks U V

theorem star_mul_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : (UpqT.mat k)ᴴ * UpqT.mat k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at hU hV
  rw [h]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU, hV]

theorem mat_inv_of_mem_Kc {k : UpqT p q} (hk : k ∈ Kc p q) : UpqT.mat k⁻¹ = (UpqT.mat k)ᴴ := by
  have h1 : UpqT.mat k * UpqT.mat k⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc UpqT.mat k⁻¹ = ((UpqT.mat k)ᴴ * UpqT.mat k) * UpqT.mat k⁻¹ := by
        rw [star_mul_of_mem_Kc hk, one_mul]
    _ = (UpqT.mat k)ᴴ := by rw [mul_assoc, h1, mul_one]

def Ksg (p q : ℕ) : Subgroup (UpqT p q) where
  carrier := Kc p q
  one_mem' := (mem_Kc_iff 1).2 ⟨1, one_mem _, 1, one_mem _, by rw [mat_one, Matrix.fromBlocks_one]⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := (mem_Kc_iff x).1 hx
    obtain ⟨U', -, V', -, h'⟩ := (mem_Kc_iff y).1 hy
    show IsKC (UpqT.mat (x * y))
    rw [mat_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (UpqT.mat x⁻¹)
    rw [mat_inv_of_mem_Kc hx]
    have hx' : IsKC (UpqT.mat x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

theorem exists_cartan (g : UpqT p q) : ∃ k ∈ Kc p q, ∃ B, g = k * eP B := by
  obtain ⟨U, hU, V, hV, h⟩ := isCartan_cartanB g
  refine ⟨g * (eP fun i j => cartanB g i j)⁻¹, (mem_Kc_iff _).2 ⟨U, hU, V, hV, ?_⟩, _,
    (inv_mul_cancel_right _ _).symm⟩
  have h1 : UpqT.mat (eP fun i j => cartanB g i j) * UpqT.mat (eP fun i j => cartanB g i j)⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [mat_mul, h, Matrix.mul_assoc]
  exact (congrArg _ h1).trans (Matrix.mul_one _)

theorem cartanB_mul_eP {k : UpqT p q} (hk : k ∈ Kc p q) (B : Fin p → Fin q → ℂ) :
    cartanB (k * eP B) = Matrix.of B := by
  obtain ⟨U, hU, V, hV, h⟩ := (mem_Kc_iff k).1 hk
  exact cartanB_eq ⟨U, hU, V, hV, by rw [mat_mul, h]; rfl⟩

theorem polJ_aOf (p q : ℕ) (h : ℕ → ℝ) :
    polJ (aOf p q h) = ∏ ab : PIx p q, shc (rootP h ab.1) := by
  set S := (sinhcAd (aOf p q h)).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hS
  set P : Matrix (PIx p q) (PIx p q) ℂ := Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1 with hP
  have key : S * P = P * Matrix.diagonal fun ab : PIx p q => ((shc (rootP h ab.1) : ℝ) : ℂ) := by
    ext cd ab
    have h1 := congrFun (sinhcAd_mulVec_of_sq_eigen p q _ _ _ (adMat_sq_mulVec_eigP p q h ab)) cd.1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Ix p q × Ix p q => ¬ sameBlock x.1 x.2)] at h1
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : {x : Ix p q × Ix p q // ¬ ¬ sameBlock x.1 x.2} =>
      sinhcAd (aOf p q h) cd.1 i.1 * eigP ab.1 i.1)
      (fun i _ => by rw [eigenvectorMatrix_eq_zero_of_sameBlock ab i.1 (not_not.1 i.2), mul_zero]), add_zero] at h1
    simp only [hS, hP, Matrix.submatrix_apply, Matrix.of_apply]
    rw [mul_comm (eigP _ _)]
    exact h1
  have h2 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm] at h2
  have h3 := mul_left_cancel₀ (det_eigenvectorMatrix_ne_zero p q) h2
  unfold polJ
  rw [← hS, h3, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem polJ_pOf (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) =
    (∏ i ∈ Finset.range (min p q), shc (2 * singVal B i) * shc (singVal B i) ^ (2 * (max p q - min p q))) *
    ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q),
      if i < j then (shc (singVal B i - singVal B j) * shc (singVal B i + singVal B j)) ^ 2 else 1 := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have e : pOf B = Matrix.fromBlocks U 0 0 V * aOf p q (singVal B) * Matrix.fromBlocks Uᴴ 0 0 Vᴴ := by
    conv_lhs => rw [hB]
    simp [aOf, pOf, singVal, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [e, Conj.polJ_conj p q _ _ _ (by simp [Matrix.fromBlocks_multiply, h1, h2]) (isKC_fromBlocks _ _)
    (isKC_fromBlocks _ _), polJ_aOf, RootProd.prod_shc_rootP]

theorem one_le_shc (x : ℝ) : 1 ≤ shc x := by
  unfold shc
  split_ifs with hx
  · exact le_rfl
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [le_div_iff_of_neg h, one_mul]; exact Real.sinh_le_self_iff.2 h.le
    · rw [le_div_iff₀ h, one_mul]; exact Real.self_le_sinh_iff.2 h.le

theorem one_le_prod_real {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl h

theorem one_le_polJ (B : Matrix (Fin p) (Fin q) ℂ) : 1 ≤ polJ (pOf B) := by
  rw [polJ_pOf]
  refine one_le_mul_of_one_le_of_one_le (one_le_prod_real fun i _ => ?_)
    (one_le_prod_real fun i _ => one_le_prod_real fun j _ => ?_)
  · exact one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_pow₀ (one_le_shc _))
  · split_ifs
    · exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_shc _) (one_le_shc _))
    · exact le_rfl

theorem shc_le_exp (x : ℝ) : shc x ≤ Real.exp |x| := by
  have key : ∀ y : ℝ, 0 < y → Real.sinh y / y ≤ Real.exp y := by
    intro y hy
    rw [div_le_iff₀ hy, Real.sinh_eq, div_le_iff₀ two_pos]
    have h1 : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(2 * y))
    have h3 := Real.exp_pos y
    rw [h1]; nlinarith
  unfold shc
  split_ifs with hx
  · exact Real.one_le_exp (abs_nonneg x)
  · rcases lt_or_gt_of_ne hx with h | h
    · have := key (-x) (neg_pos.2 h)
      rwa [Real.sinh_neg, neg_div_neg_eq, ← abs_of_neg h] at this
    · rw [abs_of_pos h]; exact key x h

theorem singVal_nonneg (B : Matrix (Fin p) (Fin q) ℂ) (i : ℕ) : 0 ≤ singVal B i :=
  LinearMap.singularValues_nonneg _ _

theorem sum_sum_ite_lt (m : ℕ) (s : ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, (if i < j then s i + s j else 0) =
      ((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (s := Finset.range (m + 1))
      (fun j hj => if_neg (by have := Finset.mem_range.1 hj; omega)), add_zero]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring

theorem polJ_le_exp (B : Matrix (Fin p) (Fin q) ℂ) : polJ (pOf B) ≤
    Real.exp (2 * (((p + q : ℕ) : ℝ) - 1) * ∑ i ∈ Finset.range (min p q), singVal B i) := by
  have h0 := singVal_nonneg B
  have hs : ∀ x, 0 ≤ shc x := fun x => zero_le_one.trans (one_le_shc x)
  rw [polJ_pOf]
  set s := singVal B
  set m := min p q with hm
  set D := max p q - min p q with hD
  have hA : ∏ i ∈ Finset.range m, shc (2 * s i) * shc (s i) ^ (2 * D) ≤
      Real.exp ((2 + 2 * (D : ℝ)) * ∑ i ∈ Finset.range m, s i) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => mul_nonneg (hs _) (pow_nonneg (hs _) _)) fun i _ => ?_
    have a1 := shc_le_exp (2 * s i)
    have a2 := shc_le_exp (s i)
    rw [abs_of_nonneg (by linarith [h0 i])] at a1 a2
    calc _ ≤ Real.exp (2 * s i) * Real.exp (s i) ^ (2 * D) :=
          mul_le_mul a1 (pow_le_pow_left₀ (hs _) a2 _) (pow_nonneg (hs _) _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hB : (∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
      if i < j then (shc (s i - s j) * shc (s i + s j)) ^ 2 else 1) ≤
      Real.exp (4 * (((m : ℝ) - 1) * ∑ i ∈ Finset.range m, s i)) := by
    rw [← sum_sum_ite_lt, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
      fun i _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
    split_ifs
    · have a1 := (shc_le_exp (s i - s j)).trans (Real.exp_le_exp.2
        (show |s i - s j| ≤ s i + s j from abs_le.2 ⟨by linarith [h0 i], by linarith [h0 j]⟩))
      have a2 := shc_le_exp (s i + s j)
      rw [abs_of_nonneg (by linarith [h0 i, h0 j])] at a2
      calc _ ≤ (Real.exp (s i + s j) * Real.exp (s i + s j)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (hs _) (hs _)) (mul_le_mul a1 a2 (hs _) (Real.exp_pos _).le) 2
        _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; push_cast; ring_nf
    · simp
  refine (mul_le_mul hA hB (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs <;> positivity) (Real.exp_pos _).le).trans (le_of_eq ?_)
  have e : ((p + q : ℕ) : ℝ) = D + 2 * m := by
    have : p + q = D + 2 * m := by omega
    exact_mod_cast this
  rw [← Real.exp_add, e]; ring_nf

end GlobalTheory.CartanInt
