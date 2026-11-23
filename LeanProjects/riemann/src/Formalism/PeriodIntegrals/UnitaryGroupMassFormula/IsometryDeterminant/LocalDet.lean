import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LocalLat

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

abbrev mR (g : Matrix ι ι K) : (ι → K) →ₗ[R] (ι → K) := g.mulVecLin.restrictScalars R

theorem mR_apply (g : Matrix ι ι K) (x : ι → K) : mR (R := R) g x = g.mulVec x := rfl

theorem mR_injective {g : Matrix ι ι K} (hg : g.det ≠ 0) : Function.Injective (mR (R := R) g) := by
  intro x y h
  have h2 := congrArg (fun v => g⁻¹.mulVec v) h
  simp only [mR_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hg),
    Matrix.one_mulVec] at h2
  exact h2

theorem mR_sat (P : HeightOneSpectrum R) (g : Matrix ι ι K) (s : R) (y : ι → K)
    (hs : s ∈ P.asIdeal.primeCompl) (hy : s • y ∈ LinearMap.range (mR (R := R) g)) :
    y ∈ LinearMap.range (mR (R := R) g) :=
  sat_of_linear P.asIdeal g.mulVecLin s y hs hy

theorem lidx_mR (P : HeightOneSpectrum R) {g : Matrix ι ι K} (hg : g.det ≠ 0)
    (A B : Submodule R (ι → K)) :
    lidx P.asIdeal (A.map (mR g)) (B.map (mR g)) = lidx P.asIdeal A B :=
  lidx_map P.asIdeal (mR g) (mR_injective hg) (mR_sat P g) A B

theorem map_mR_mul (g h : Matrix ι ι K) (A : Submodule R (ι → K)) :
    (A.map (mR h)).map (mR g) = A.map (mR (g * h)) := by
  rw [← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, mR_apply, mR_apply, mR_apply, Matrix.mulVec_mulVec]

theorem map_mR_one (A : Submodule R (ι → K)) : A.map (mR (1 : Matrix ι ι K)) = A := by
  have : mR (R := R) (1 : Matrix ι ι K) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.id_apply, mR_apply, Matrix.one_mulVec]
  rw [this, Submodule.map_id]

theorem std_eq : (std : Submodule R (ι → K)) =
    Submodule.pi Set.univ (fun _ : ι => ((1 : FI) : Submodule R K)) := by
  simp only [std, FractionalIdeal.coe_one]

theorem isLat_std : IsLat (std : Submodule R (ι → K)) := by
  rw [std_eq]; exact isLat_pi (fun _ => 1) (fun _ => one_ne_zero)

variable (R) in

def chi (P : HeightOneSpectrum R) (g : Matrix ι ι K) : ℤ :=
  lidx P.asIdeal (std : Submodule R (ι → K)) ((std : Submodule R (ι → K)).map (mR g))

theorem chi_one (P : HeightOneSpectrum R) : chi R P (1 : Matrix ι ι K) = 0 := by
  rw [chi, map_mR_one, lidx_self]

theorem chi_mul (P : HeightOneSpectrum R) {g h : Matrix ι ι K} (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    chi R P (g * h) = chi R P g + chi R P h := by
  have hgh : (g * h).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hg hh
  unfold chi
  rw [← map_mR_mul, lat_cocycle P (B := (std : Submodule R (ι → K)).map (mR g)) isLat_std
    (isLat_map g hg isLat_std) (isLat_map g hg (isLat_map h hh isLat_std)), lidx_mR P hg]

theorem map_std_le {g : Matrix ι ι K} (hg : ∀ a b, ∃ z : R, algebraMap R K z = g a b) :
    (std : Submodule R (ι → K)).map (mR g) ≤ std := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ∀ b, ∃ w : R, algebraMap R K w = y b := fun b =>
    Submodule.mem_one.mp ((Submodule.mem_pi.mp hy) b (Set.mem_univ b))
  choose w hw using hy'
  choose z hz using hg
  refine Submodule.mem_pi.mpr (fun a _ => Submodule.mem_one.mpr ?_)
  refine ⟨∑ b, z a b * w b, ?_⟩
  rw [mR_apply, Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, hz, hw]

theorem map_std_eq {g g' : Matrix ι ι K} (hg : ∀ a b, ∃ z : R, algebraMap R K z = g a b)
    (hg' : ∀ a b, ∃ z : R, algebraMap R K z = g' a b) (hgg' : g * g' = 1) :
    (std : Submodule R (ι → K)).map (mR g) = std := by
  refine le_antisymm (map_std_le hg) (fun y hy => ?_)
  refine ⟨g'.mulVec y, map_std_le hg' ⟨y, hy, rfl⟩, ?_⟩
  simp [mR_apply, Matrix.mulVec_mulVec, hgg']

theorem chi_transvection_int (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (z : R) :
    chi R P (Matrix.transvection i j (algebraMap R K z)) = 0 := by
  have hint : ∀ c : R, ∀ a b, ∃ w : R, algebraMap R K w = Matrix.transvection i j (algebraMap R K c) a b := by
    intro c a b
    refine ⟨Matrix.transvection i j c a b, ?_⟩
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [chi, map_std_eq (hint z) (g' := Matrix.transvection i j (algebraMap R K (-z))) (hint (-z))
    (by rw [Matrix.transvection_mul_transvection_same i j hij, ← map_add, add_neg_cancel, map_zero,
      Matrix.transvection_zero]), lidx_self]

theorem chi_transvection (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (c : K) :
    chi R P (Matrix.transvection i j c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, Matrix.transvection_zero, chi_one]
  set D : Matrix ι ι K := Matrix.diagonal (Function.update 1 i c)
  set D' : Matrix ι ι K := Matrix.diagonal (Function.update 1 i c⁻¹)
  have hDD' : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    by_cases ha : a = i
    · subst ha; simp [hc]
    · simp [Function.update_of_ne ha]
  have hdet : ∀ M N : Matrix ι ι K, M * N = 1 → M.det ≠ 0 := fun M N h hM => by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, hM, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hD : D.det ≠ 0 := hdet D D' hDD'
  have hD'D : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    by_cases ha : a = i
    · subst ha; simp [hc]
    · simp [Function.update_of_ne ha]
  have hD' : D'.det ≠ 0 := hdet D' D hD'D
  have ht1 : (Matrix.transvection i j (1 : K)).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero
  have he : Matrix.transvection i j c = D * Matrix.transvection i j 1 * D' := by
    ext a b
    simp only [D, D', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    rcases eq_or_ne a i with rfl | ha
    · rcases eq_or_ne b a with rfl | hba
      · simp [Function.update_self, hij.symm]
        field_simp
      · rcases eq_or_ne b j with rfl | hbj
        · simp [Function.update_self, Function.update_of_ne hba, hba.symm]
        · simp [hba.symm, hbj.symm]
    · rcases eq_or_ne a b with rfl | hab
      · simp [Function.update_of_ne ha, ha.symm]
      · simp [hab, ha.symm, Function.update_of_ne ha]
  have h1 := chi_transvection_int (K := K) P hij 1
  rw [map_one] at h1
  rw [he, chi_mul P (by rw [Matrix.det_mul]; exact mul_ne_zero hD ht1) hD', chi_mul P hD ht1, h1,
    add_zero, ← chi_mul P hD hD', hDD', chi_one]

theorem std_map_diagonal (D : ι → K) :
    (std : Submodule R (ι → K)).map (mR (Matrix.diagonal D)) =
      Submodule.pi Set.univ (fun i => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) : FI) :
        Submodule R K)) := by
  ext x
  simp only [Submodule.mem_map, std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_spanSingleton, mR_apply, Matrix.mulVec_diagonal]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨w, hw⟩ := hy i
    exact ⟨w, by rw [Matrix.mulVec_diagonal, Algebra.smul_def, hw, mul_comm]⟩
  · intro h
    choose w hw using h
    refine ⟨fun i => algebraMap R K (w i), fun i => ⟨w i, rfl⟩, ?_⟩
    ext i
    rw [Matrix.mulVec_diagonal, ← hw i, Algebra.smul_def, mul_comm]

theorem count_spanSingleton_prod (P : HeightOneSpectrum R) (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i)) =
      ∑ i, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i)) := by
  have : FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i) =
      ∏ i, FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton, ih]
  rw [this, FractionalIdeal.count_prod K P _ _ (fun i _ =>
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hD i))]

theorem chi_diagonal (P : HeightOneSpectrum R) (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    chi R P (Matrix.diagonal D) =
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i)) := by
  rw [chi, std_map_diagonal, std_eq, lidx_pi_frac P (fun _ => 1)
    (fun i => FractionalIdeal.spanSingleton _ (D i)) (fun _ => one_ne_zero)
    (fun i => FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hD i)), count_spanSingleton_prod P D hD]
  simp [FractionalIdeal.count_one]

theorem chi_eq (P : HeightOneSpectrum R) (g : Matrix ι ι K) (hg : g.det ≠ 0) :
    chi R P g = FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) g.det) := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => chi R P M = FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) M.det))
    g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      intro i hi
      rw [Matrix.det_diagonal] at hD
      exact hD (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    rw [chi_diagonal P D hD', Matrix.det_diagonal]
  · intro t
    rw [Matrix.TransvectionStruct.det, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
    exact chi_transvection P t.hij t.c
  · intro A B hA hB hA' hB'
    rw [chi_mul P hA hB, hA', hB', Matrix.det_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hA)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hB)]

end PI.IsoDetW.Loc
