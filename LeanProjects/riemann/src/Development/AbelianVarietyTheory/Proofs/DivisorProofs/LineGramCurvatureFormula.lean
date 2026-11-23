import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram

open Matrix Complex ComplexConjugate Filter Topology GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.CholFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {n : Type*} [Fintype n] [DecidableEq n]

def cholB (P : E → Matrix n n ℂ) (x η : E) : Matrix n n ℂ := mdbar P x η * (P x)⁻¹

def cholC (P : E → Matrix n n ℂ) (x ξ : E) : Matrix n n ℂ := (cholB P x ξ)ᴴ

def cholX (P : E → Matrix n n ℂ) (y ξ η : E) : Matrix n n ℂ :=
  cholB P y η * cholC P y ξ - cholC P y ξ * cholB P y η - mdbar (fun x => cholC P x ξ) y η
    - mdel (fun x => cholB P x η) y ξ

theorem conn_chol {P : E → Matrix n n ℂ} {y : E} (h : MContDiffAt 1 P y)
    (hu : IsUnit (P y).det) (ξ : E) :
    conn (fun x => (P x)ᵀ * (P x)ᴴᵀ) y ξ =
      (P y)⁻¹ * (cholC P y ξ + mdel P y ξ * (P y)⁻¹) * P y := by
  have e1 : ∀ x, ((P x)ᵀ * (P x)ᴴᵀ)ᵀ = (P x)ᴴ * P x := fun x => by
    rw [transpose_mul, transpose_transpose]; rfl
  have hu' : IsUnit (P y)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
  rw [conn, ← mdel_transpose]
  simp only [e1]
  rw [mdel_mul h.conjTranspose h, mdel_conjTranspose, cholC, cholB, Matrix.mul_inv_rev,
    conjTranspose_mul, conjTranspose_nonsing_inv]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hu', nonsing_inv_mul_cancel_left _ _ hu,
    nonsing_inv_mul _ hu, Matrix.mul_one]
  abel

end GlobalTheory.CholFrame

namespace GlobalTheory.CholFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {n : Type*} [Fintype n] [DecidableEq n]

theorem curv_chol {P : E → Matrix n n ℂ} {y : E} (h : MContDiffAt 2 P y)
    (hu : IsUnit (P y).det) (ξ η : E) :
    curv (fun x => (P x)ᵀ * (P x)ᴴᵀ) y ξ η = (P y)⁻¹ * cholX P y ξ η * P y := by
  have h1 : MContDiffAt 1 P y := h.of_le one_le_two
  have he : (fun x => conn (fun x => (P x)ᵀ * (P x)ᴴᵀ) x ξ) =ᶠ[𝓝 y]
      fun x => (P x)⁻¹ * ((cholC P x ξ + mdel P x ξ * (P x)⁻¹) * P x) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h2 h3
    rw [conn_chol (h2.of_le one_le_two) h3 ξ, Matrix.mul_assoc]
  have hi : MContDiffAt 1 (fun x => (P x)⁻¹) y := h1.inv hu
  have hdb : ∀ v, MContDiffAt 1 (fun x => mdbar P x v) y := fun v => h.mdbar (by norm_num) v
  have hd : MContDiffAt 1 (fun x => mdel P x ξ) y := h.mdel (by norm_num) ξ
  have hC : MContDiffAt 1 (fun x => cholC P x ξ) y :=
    ((hdb ξ).mul hi).conjTranspose
  have hD : MContDiffAt 1 (fun x => mdel P x ξ * (P x)⁻¹) y := hd.mul hi
  have hB := mdel_mul (hdb η) hi ξ
  rw [mdel_mdbar h, mdel_inv h1 hu] at hB
  have hD' := mdbar_mul hd hi η
  rw [mdbar_mdel h, mdbar_inv h1 hu] at hD'
  rw [curv, mdbar_congr he, mdbar_mul hi ((hC.add hD).mul h1), mdbar_inv h1 hu,
    mdbar_mul (hC.add hD) h1, mdbar_add hC hD, hD', cholX, cholB,
    show mdel (fun x => cholB P x η) y ξ = _ from hB]
  simp only [cholB, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu,
    nonsing_inv_mul _ hu, Matrix.mul_one]
  abel

end GlobalTheory.CholFrame

namespace GlobalTheory.CholFrame

theorem firstGram_chol {N k : ℕ} (hk : k ≤ N) (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.BlockTriangular id) :
    firstGram hk (Sᵀ * Sᴴᵀ) = (firstGram hk S)ᵀ * (firstGram hk S)ᴴᵀ := by
  ext a b
  simp only [firstGram, submatrix_apply, mul_apply, transpose_apply, conjTranspose_apply]
  symm
  refine Eq.trans (Finset.sum_map Finset.univ (Fin.castLEEmb hk)
    (fun m => S m (Fin.castLE hk a) * (star (S m (Fin.castLE hk b))))).symm ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
  have : a.val < m.val := by
    by_contra hc
    exact hm (Finset.mem_map.2 ⟨⟨m.val, by have := a.2; omega⟩, Finset.mem_univ _,
      Fin.ext rfl⟩)
  have h0 : S m (Fin.castLE hk a) = 0 := hS (show Fin.castLE hk a < m from this)
  simp [h0]

theorem det_firstGram_chol {N k : ℕ} (hk : k ≤ N) (S : Matrix (Fin N) (Fin N) ℂ)
    (hS : S.BlockTriangular id) :
    (firstGram hk (Sᵀ * Sᴴᵀ)).det =
      ∏ m : Fin k, S (Fin.castLE hk m) (Fin.castLE hk m) * conj (S (Fin.castLE hk m) (Fin.castLE hk m)) := by
  have ht : (firstGram hk S).BlockTriangular id := fun a b hab => hS (show Fin.castLE hk b < Fin.castLE hk a from hab)
  rw [firstGram_chol hk S hS, det_mul, det_transpose, det_transpose, det_conjTranspose,
    det_of_upperTriangular ht, Finset.prod_mul_distrib]
  congr 1
  rw [star_prod]
  rfl

theorem gradedGram_chol {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.BlockTriangular id)
    (hd : ∀ j, S j j ≠ 0) (i : Fin N) :
    gradedGram (Sᵀ * Sᴴᵀ) i () () = S i i * conj (S i i) := by
  have hne : ∀ j, S j j * conj (S j j) ≠ 0 := fun j => mul_ne_zero (hd j) (by simpa using hd j)
  have h0 : (firstGram i.2.le (Sᵀ * Sᴴᵀ)).det ≠ 0 := by
    rw [det_firstGram_chol _ S hS]; exact Finset.prod_ne_zero_iff.2 fun m _ => hne _
  have h := det_firstGram_succ (Sᵀ * Sᴴᵀ) i (Ne.isUnit h0)
  rw [det_firstGram_chol _ S hS, det_firstGram_chol _ S hS, Fin.prod_univ_castSucc] at h
  have hl : Fin.castLE i.2 (Fin.last i) = i := Fin.ext rfl
  rw [hl] at h
  have h0' : ∏ m : Fin i, S (Fin.castLE i.2.le m) (Fin.castLE i.2.le m) *
      conj (S (Fin.castLE i.2.le m) (Fin.castLE i.2.le m)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m _ => hne _
  exact (mul_left_cancel₀ h0' h.symm)

end GlobalTheory.CholFrame

namespace GlobalTheory.GradedLine

open GlobalTheory.CholFrame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ} {U : Set (ι → ℂ)}
  {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E} {π : E → ι → ℂ}
  {A e : E → Matrix (Fin n) (Fin n) ℂ}

theorem gram_frame (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    (e x)ᵀ * H (π x) * (e x)ᴴᵀ = 1 := by
  ext k l
  have := he.unitary x hx k l
  rw [form_eq_sum] at this
  rw [one_apply, ← this]
  simp only [mul_apply, transpose_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem isUnit_det_frame (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    IsUnit (e x).det := by
  have h := congrArg det (gram_frame he hx)
  rw [det_mul, det_mul, det_one, det_transpose, mul_assoc] at h
  exact isUnit_iff_exists_inv.2 ⟨_, h⟩

theorem inv_frame (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    (e x)⁻¹ = (H (π x) * (e x)ᴴᵀ)ᵀ := by
  have h := congrArg transpose (gram_frame he hx)
  rw [Matrix.mul_assoc, transpose_mul, transpose_transpose, transpose_one] at h
  exact inv_eq_left_inv h

theorem gram_eq_inv (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    H (π x) = ((e x)⁻¹)ᵀ * ((e x)⁻¹)ᴴᵀ := by
  have hu := isUnit_det_frame he hx
  have h1 : IsUnit (e x)ᵀ.det := by rwa [det_transpose]
  have h2 : IsUnit (e x)ᴴᵀ.det := by rw [det_transpose, det_conjTranspose]; exact hu.star
  calc H (π x) = ((e x)ᵀ)⁻¹ * ((e x)ᵀ * H (π x) * (e x)ᴴᵀ) * ((e x)ᴴᵀ)⁻¹ := by
        simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ h1, mul_nonsing_inv _ h2,
          Matrix.mul_one]
    _ = _ := by
        rw [gram_frame he hx, Matrix.mul_one, transpose_nonsing_inv, conjTranspose_nonsing_inv,
          transpose_nonsing_inv]

theorem factor_apply (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) (k i : Fin n) :
    ((e x)⁻¹ * A x) k i = form (H (π x)) (fun a => A x a i) (fun a => e x a k) := by
  rw [inv_frame he hx, form_eq_sum]
  simp only [mul_apply, transpose_apply, conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def]; ring

theorem factor_triangular (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    ((e x)⁻¹ * A x).BlockTriangular id := by
  intro k i hik
  rw [factor_apply he hx, ← conj_form (hH.posDef _ (hF.mapsTo hx)).isHermitian,
    he.perp x hx k i hik, map_zero]

theorem adaptedGram_eq (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    adaptedGram H π A x = ((e x)⁻¹ * A x)ᵀ * ((e x)⁻¹ * A x)ᴴᵀ := by
  have hu := isUnit_det_frame he hx
  have hg := gram_frame he hx
  have hA : A x = e x * ((e x)⁻¹ * A x) := (mul_nonsing_inv_cancel_left _ _ hu).symm
  generalize (e x)⁻¹ * A x = S at hA ⊢
  generalize e x = f at hA hg ⊢
  rw [adaptedGram, hA, transpose_mul, conjTranspose_mul, transpose_mul]
  calc Sᵀ * fᵀ * H (π x) * (fᴴᵀ * Sᴴᵀ) = Sᵀ * (fᵀ * H (π x) * fᴴᵀ) * Sᴴᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_one]

theorem factor_diag_ne (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) (j : Fin n) :
    ((e x)⁻¹ * A x) j j ≠ 0 := by
  have h : IsUnit ((e x)⁻¹ * A x).det := by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (isUnit_det_frame he hx)).mul (hF.isUnit x hx)
  rw [det_of_upperTriangular (factor_triangular hH hF he hx)] at h
  exact Finset.prod_ne_zero_iff.1 h.ne_zero j (Finset.mem_univ _)

end GlobalTheory.GradedLine

namespace GlobalTheory.GradedLine

open GlobalTheory.CholFrame

theorem mul_diag_of_tri {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℂ} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (i : Fin n) : (M * N) i i = M i i * N i i := by
  rw [mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hM h, zero_mul]
  · rw [hN h, mul_zero]

theorem inv_diag_of_tri {n : ℕ} {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.BlockTriangular id)
    (hu : IsUnit S.det) (i : Fin n) : S⁻¹ i i = (S i i)⁻¹ := by
  letI := invertibleOfIsUnitDet _ hu
  have ht : S⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular hS
  have h := congrFun (congrFun (mul_nonsing_inv S hu) i) i
  rw [mul_diag_of_tri hS ht, one_apply_eq] at h
  exact eq_inv_of_mul_eq_one_right h

theorem sum_eq_sum_Ioi_add {n : ℕ} (f : Fin n → ℂ) (i : Fin n) (hf : ∀ l, l < i → f l = 0) :
    ∑ l, f l = ∑ l ∈ Finset.Ioi i, f l + f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => i < l), Finset.filter_lt_eq_Ioi]
  congr 1
  refine Finset.sum_eq_single i (fun l hl hli => hf l ?_) (fun h => absurd (by simp) h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hl
  exact lt_of_le_of_ne hl hli

theorem sum_eq_sum_Iio_add {n : ℕ} (f : Fin n → ℂ) (i : Fin n) (hf : ∀ l, i < l → f l = 0) :
    ∑ l, f l = ∑ l ∈ Finset.Iio i, f l + f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l < i), Finset.filter_gt_eq_Iio]
  congr 1
  refine Finset.sum_eq_single i (fun l hl hli => hf l ?_) (fun h => absurd (by simp) h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hl
  exact lt_of_le_of_ne hl (Ne.symm hli)

theorem cholB_unit {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (f : E → ℂ) {x : E} (hx : f x ≠ 0) (v : E) :
    cholB (fun x => (of fun _ _ => f x : Matrix Unit Unit ℂ)) x v () () =
      dbar f x v * (f x)⁻¹ := by
  have hu : IsUnit (of fun _ _ => f x : Matrix Unit Unit ℂ).det := by
    rw [det_unique]; exact Ne.isUnit hx
  have h := congrFun (congrFun (nonsing_inv_mul _ hu) ()) ()
  simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton, of_apply, one_apply_eq] at h
  have hi := eq_inv_of_mul_eq_one_left h
  simp only [cholB, mul_apply, Finset.univ_unique, Finset.sum_singleton, mdbar_apply, of_apply]
  exact congrArg (dbar f x v * ·) hi

end GlobalTheory.GradedLine

namespace GlobalTheory.GradedLine

open GlobalTheory.CholFrame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ} {U : Set (ι → ℂ)}
  {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E} {π : E → ι → ℂ}
  {A e : E → Matrix (Fin n) (Fin n) ℂ}

theorem frame_smooth (hF : IsFlagFamily Y U π A) (he : IsUnitaryFlagFrame Y H π A e) {x : E}
    (hx : x ∈ Y) : MContDiffAt ∞ e x :=
  fun a b => (he.smooth a b).contDiffAt (hF.isOpen.mem_nhds hx)

theorem adapted_smooth (hF : IsFlagFamily Y U π A) {x : E} (hx : x ∈ Y) : MContDiffAt ∞ A x :=
  fun a b => ((hF.hol_frame a b).contDiffAt (hF.isOpen.mem_nhds hx)).restrict_scalars ℝ

theorem mdbar_adapted (hF : IsFlagFamily Y U π A) {x : E} (hx : x ∈ Y) (η : E) :
    mdbar A x η = 0 := by
  ext a b
  rw [mdbar_apply, dbar_eq_zero (((hF.hol_frame a b).contDiffAt
    (hF.isOpen.mem_nhds hx)).differentiableAt (by simp))]
  rfl

theorem cholB_factor (hF : IsFlagFamily Y U π A) (he : IsUnitaryFlagFrame Y H π A e) {x : E}
    (hx : x ∈ Y) (η : E) :
    cholB (fun x => (e x)⁻¹ * A x) x η = cholB (fun x => (e x)⁻¹) x η := by
  have hu := isUnit_det_frame he hx
  have hA : MContDiffAt 1 A x := (adapted_smooth hF hx).of_le (by norm_cast)
  have hei : MContDiffAt 1 (fun x => (e x)⁻¹) x :=
    (((frame_smooth hF he hx).of_le (by norm_cast)).inv hu)
  rw [cholB, cholB, mdbar_mul hei hA, mdbar_adapted hF hx, Matrix.mul_zero, zero_add,
    Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ (hF.isUnit x hx)]

theorem cholB_factor_tri (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) (η : E) :
    (cholB (fun x => (e x)⁻¹ * A x) x η).BlockTriangular id := by
  have hS := factor_triangular hH hF he hx
  have hu : IsUnit ((e x)⁻¹ * A x).det := by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (isUnit_det_frame he hx)).mul (hF.isUnit x hx)
  letI := invertibleOfIsUnitDet _ hu
  refine BlockTriangular.mul (fun k i hik => ?_) (blockTriangular_inv_of_blockTriangular hS)
  rw [mdbar_apply, dbar_congr (g := fun _ => (0 : ℂ))
    (Filter.eventually_of_mem (hF.isOpen.mem_nhds hx) fun x' hx' =>
      factor_triangular hH hF he hx' hik), dbar_const]
  rfl

theorem cholB_diag (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) (η : E) (i : Fin n) :
    cholB (fun x => (e x)⁻¹) x η i i =
      dbar (fun x => ((e x)⁻¹ * A x) i i) x η * (((e x)⁻¹ * A x) i i)⁻¹ := by
  have hS := factor_triangular hH hF he hx
  have hu : IsUnit ((e x)⁻¹ * A x).det := by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (isUnit_det_frame he hx)).mul (hF.isUnit x hx)
  letI := invertibleOfIsUnitDet _ hu
  have hd : (mdbar (fun x => (e x)⁻¹ * A x) x η).BlockTriangular id := fun k j hjk => by
    rw [mdbar_apply, dbar_congr (g := fun _ => (0 : ℂ))
      (Filter.eventually_of_mem (hF.isOpen.mem_nhds hx) fun x' hx' =>
        factor_triangular hH hF he hx' hjk), dbar_const]
    rfl
  rw [← cholB_factor hF he hx, cholB, mul_diag_of_tri hd (blockTriangular_inv_of_blockTriangular hS),
    inv_diag_of_tri hS hu]
  rfl

end GlobalTheory.GradedLine

namespace GlobalTheory.GradedLine

open GlobalTheory.CholFrame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ} {U : Set (ι → ℂ)}
  {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E} {π : E → ι → ℂ}
  {A e : E → Matrix (Fin n) (Fin n) ℂ}

theorem gram_eventually (hF : IsFlagFamily Y U π A) (he : IsUnitaryFlagFrame Y H π A e)
    {y : E} (hy : y ∈ Y) :
    (fun x => H (π x)) =ᶠ[𝓝 y] fun x => ((e x)⁻¹)ᵀ * ((e x)⁻¹)ᴴᵀ :=
  Filter.eventually_of_mem (hF.isOpen.mem_nhds hy) fun _ hx => gram_eq_inv he hx

theorem thetaOneZero_eq (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {y : E} (hy : y ∈ Y) (ξ : E) :
    thetaOneZero H π e y ξ = cholC (fun x => (e x)⁻¹) y ξ := by
  have hu := isUnit_det_frame he hy
  have hK := hH.isHermFrame.mContDiffAt (hF.mapsTo hy)
  have hπ : ContDiffAt ℂ ∞ π y := hF.hol_proj.contDiffAt (hF.isOpen.mem_nhds hy)
  have he' := frame_smooth hF he hy
  have hP : MContDiffAt 1 (fun x => (e x)⁻¹) y := (he'.of_le (by norm_cast)).inv hu
  rw [thetaOneZero, ← conn_comp_holo (hK.of_le (by norm_cast)) (hπ.differentiableAt (by simp)),
    conn_congr (gram_eventually hF he hy), conn_chol hP (isUnit_nonsing_inv_det _ hu)]
  rw [nonsing_inv_nonsing_inv _ hu, mdel_inv (he'.of_le (by norm_cast)) hu]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hu, nonsing_inv_mul _ hu, Matrix.mul_one]
  abel

theorem curvDiag_eq (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {y : E} (hy : y ∈ Y) (i : Fin n) (ξ η : E) :
    curvDiag H π e i y ξ η = cholX (fun x => (e x)⁻¹) y ξ η i i := by
  have hu := isUnit_det_frame he hy
  have hK := hH.isHermFrame.mContDiffAt (hF.mapsTo hy)
  have hπ : ContDiffAt ℂ ∞ π y := hF.hol_proj.contDiffAt (hF.isOpen.mem_nhds hy)
  have he' := frame_smooth hF he hy
  have hP : MContDiffAt 2 (fun x => (e x)⁻¹) y := (he'.of_le (by norm_cast)).inv hu
  rw [curvDiag, ← curv_comp_holo (hK.of_le (by norm_cast))
      (hH.isHermFrame.isUnit _ (hF.mapsTo hy)) (hπ.of_le (by norm_cast)),
    curv_congr (gram_eventually hF he hy), curv_chol hP (isUnit_nonsing_inv_det _ hu)]
  rw [nonsing_inv_nonsing_inv _ hu]
  have hc : (fun a => e y a i) = e y *ᵥ Pi.single i 1 := by
    ext a; simp [mulVec, dotProduct, Pi.single_apply]
  rw [hc, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu,
    Matrix.mul_one, ← mulVec_mulVec, form_mulVec, gram_frame he hy, one_mulVec]
  simp [mulVec, dotProduct, Pi.single_apply]

end GlobalTheory.GradedLine

namespace GlobalTheory.GradedLine

open GlobalTheory.CholFrame

theorem unit_conj {M : Matrix Unit Unit ℂ} (hu : IsUnit M.det) (X : Matrix Unit Unit ℂ) :
    M⁻¹ * X * M = X := by
  have h : M⁻¹ * X = X * M⁻¹ := by ext ⟨⟩ ⟨⟩; simp [mul_apply, mul_comm]
  rw [h, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

theorem unit_comm (X Z : Matrix Unit Unit ℂ) : X * Z = Z * X := by
  ext ⟨⟩ ⟨⟩; simp [mul_apply, mul_comm]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ} {U : Set (ι → ℂ)}
  {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E} {π : E → ι → ℂ}
  {A e : E → Matrix (Fin n) (Fin n) ℂ}

theorem curv_line_eq (hH : IsPosFrame U H) (hF : IsFlagFamily Y U π A)
    (he : IsUnitaryFlagFrame Y H π A e) {y : E} (hy : y ∈ Y) (i : Fin n) (ξ η : E) :
    curv (lineGram H π A i) y ξ η () () =
      -mdbar (fun x => cholC (fun x => (e x)⁻¹) x ξ) y η i i
        - mdel (fun x => cholB (fun x => (e x)⁻¹) x η) y ξ i i := by
  have hu := isUnit_det_frame he hy
  have hSs : MContDiffAt ∞ (fun x => (e x)⁻¹ * A x) y :=
    ((frame_smooth hF he hy).inv hu).mul (adapted_smooth hF hy)
  have hs2 : MContDiffAt 2 (fun x => (of fun _ _ => ((e x)⁻¹ * A x) i i : Matrix Unit Unit ℂ)) y :=
    fun _ _ => (hSs i i).of_le (by norm_cast)
  have hsu : IsUnit (of fun _ _ => ((e y)⁻¹ * A y) i i : Matrix Unit Unit ℂ).det := by
    rw [det_unique]; exact Ne.isUnit (factor_diag_ne hH hF he hy i)
  have hl : lineGram H π A i =ᶠ[𝓝 y] fun x =>
      (of fun _ _ => ((e x)⁻¹ * A x) i i : Matrix Unit Unit ℂ)ᵀ *
        (of fun _ _ => ((e x)⁻¹ * A x) i i : Matrix Unit Unit ℂ)ᴴᵀ :=
    Filter.eventually_of_mem (hF.isOpen.mem_nhds hy) fun x hx => by
      ext ⟨⟩ ⟨⟩
      rw [lineGram, adaptedGram_eq he hx, gradedGram_chol _ (factor_triangular hH hF he hx)
        (factor_diag_ne hH hF he hx)]
      simp [mul_apply]
  have hB : (fun x => cholB (fun x => (of fun _ _ => ((e x)⁻¹ * A x) i i : Matrix Unit Unit ℂ))
      x η () ()) =ᶠ[𝓝 y] fun x => cholB (fun x => (e x)⁻¹) x η i i :=
    Filter.eventually_of_mem (hF.isOpen.mem_nhds hy) fun x hx => by
      beta_reduce
      exact (cholB_unit (fun x => ((e x)⁻¹ * A x) i i) (factor_diag_ne hH hF he hx i) η).trans
        (cholB_diag hH hF he hx η i).symm
  have hC : (fun x => cholC (fun x => (of fun _ _ => ((e x)⁻¹ * A x) i i : Matrix Unit Unit ℂ))
      x ξ () ()) =ᶠ[𝓝 y] fun x => cholC (fun x => (e x)⁻¹) x ξ i i :=
    Filter.eventually_of_mem (hF.isOpen.mem_nhds hy) fun x hx => by
      beta_reduce
      simp only [cholC, conjTranspose_apply]
      exact congrArg star ((cholB_unit (fun x => ((e x)⁻¹ * A x) i i)
        (factor_diag_ne hH hF he hx i) ξ).trans (cholB_diag hH hF he hx ξ i).symm)
  rw [curv_congr hl, curv_chol hs2 hsu, unit_conj hsu, cholX, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
    unit_comm (cholB _ y η), sub_self, zero_sub, mdbar_apply, mdel_apply, mdbar_apply,
    mdel_apply, dbar_congr hC, del_congr hB]

theorem curv_lineGram : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y, ∀ i ξ η, curv (lineGram H π A i) y ξ η () () =
      curvDiag H π e i y ξ η - ∑ l ∈ Finset.Ioi i, thetaSq H π e l i y ξ η
        + ∑ l ∈ Finset.Iio i, thetaSq H π e i l y ξ η := by
  intro E _ _ _ _ _ ι _ n U H Y π A e hH hF he y hy i ξ η
  have htri : (cholB (fun x => (e x)⁻¹) y η).BlockTriangular id :=
    cholB_factor hF he hy η ▸ cholB_factor_tri hH hF he hy η
  have hθ : ∀ v, thetaOneZero H π e y v = cholC (fun x => (e x)⁻¹) y v :=
    thetaOneZero_eq hH hF he hy
  rw [curv_line_eq hH hF he hy i ξ η, curvDiag_eq hH hF he hy i ξ η, cholX, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.sub_apply, mul_apply, mul_apply]
  simp only [thetaSq, hθ]
  simp only [cholC, conjTranspose_apply, Complex.star_def, conj_conj]
  generalize cholB (fun x => (e x)⁻¹) y η = b at htri ⊢
  rw [sum_eq_sum_Ioi_add (fun l => b i l * conj (cholB (fun x => (e x)⁻¹) y ξ i l)) i
      (fun l hl => by simp only [htri hl, zero_mul]),
    sum_eq_sum_Iio_add (fun l => conj (cholB (fun x => (e x)⁻¹) y ξ l i) * b l i) i
      (fun l hl => by simp only [htri hl, mul_zero])]
  simp only [mul_comm (b _ _)]
  ring

end GlobalTheory.GradedLine
