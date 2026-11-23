import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.Single

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K]

theorem existsUnique_triangular {ι : Type*} [Fintype ι] (ord : ι → ℕ)
    {S : (ι → 𝔸[K]) → (ι → 𝔸[K])} (s : ι → (ι → 𝔸[K]) → 𝔸[K]) (hS : ∀ z i, S z i = z i + s i z)
    (hs : ∀ i z z', (∀ j, ord j < ord i → z j = z' j) → s i z = s i z') (y : ι → 𝔸[K]) :
    ∃! g : vecLattice K ι, S (g +ᵥ y) ∈ vecDomain K ι := by
  classical
  set F := GroundTheory.Global.fundamentalSet K
  set A : (ι → K) → ι → 𝔸[K] := fun l i => algebraMap K 𝔸[K] (l i)

  have hex : ∀ N : ℕ, ∃ l : ι → K, ∀ i, ord i < N → S (A l + y) i ∈ F := by
    intro N
    induction N with
    | zero => exact ⟨0, fun i h => absurd h (Nat.not_lt_zero _)⟩
    | succ N ih =>
      obtain ⟨l, hl⟩ := ih
      choose c hc _ using fun i => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (S (A l + y) i)
      set l' : ι → K := fun i => if ord i = N then l i - c i else l i
      have hagree : ∀ i j, ord j < ord i → ord i ≤ N → l' j = l j := by
        intro i j hj hi
        simp only [l', if_neg (show ord j ≠ N by omega)]
      refine ⟨l', fun i hi => ?_⟩
      have hsi : s i (A l' + y) = s i (A l + y) := hs i _ _ fun j hj => by
        simp only [A, Pi.add_apply, hagree i j hj (by omega)]
      rw [hS, hsi]
      by_cases hN : ord i = N
      · simp only [A, Pi.add_apply, l', if_pos hN, map_sub]
        have := hc i
        rw [hS] at this
        convert this using 1
        simp only [A, Pi.add_apply]
        ring
      · simp only [A, Pi.add_apply, l', if_neg hN]
        have := hl i (by omega)
        rwa [hS] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ i, ord i < N :=
    ⟨Finset.univ.sup ord + 1, fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  obtain ⟨l, hl⟩ := hex N
  refine ⟨⟨A l, l, rfl⟩, fun i _ => hl i (hN i), ?_⟩

  rintro ⟨_, m, rfl⟩ hm
  have key : ∀ M i, ord i < M → m i = l i := by
    intro M
    induction M with
    | zero => intro i h; exact absurd h (Nat.not_lt_zero _)
    | succ M ih =>
      intro i hi
      have hsi : s i (A m + y) = s i (A l + y) := hs i _ _ fun j hj => by
        simp only [A, Pi.add_apply, ih j (by omega)]
      have h1 := hm i (mem_univ i)
      have h2 := hl i (hN i)
      change S ((fun i => algebraMap K 𝔸[K] (m i)) + y) i ∈ F at h1
      rw [hS] at h1 h2
      rw [show ((fun i => algebraMap K 𝔸[K] (m i)) + y) = A m + y from rfl, hsi] at h1
      obtain ⟨c, -, hcu⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (y i + s i (A l + y))
      have e1 : -m i = -l i := by
        have a1 := hcu (-m i) (by
          simp only [A, Pi.add_apply] at h1
          convert h1 using 1; rw [map_neg]; ring)
        have a2 := hcu (-l i) (by
          simp only [A, Pi.add_apply] at h2
          convert h2 using 1; rw [map_neg]; ring)
        rw [a1, a2]
      exact neg_injective e1
  refine Subtype.ext (funext fun i => ?_)
  show algebraMap K 𝔸[K] (m i) = algebraMap K 𝔸[K] (l i)
  rw [key N i (hN i)]

variable {n : ℕ}

section Shear

variable {k : ℕ} (B : LowPos n k → 𝔸[K])

theorem blockEntry_eq_of_vanishing {X : Matrix (Fin n) (Fin n) 𝔸[K]}
    (hX : ∀ i j : Fin n, ¬ ((i : ℕ) < k ∧ k ≤ (j : ℕ)) → X i j = 0) :
    blockEntry (fun u : UPos n k => X u.1.1 u.1.2) = X := by
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · exact (hX i j h).symm

theorem uMat_extLow_apply_of_lt (i j : Fin n) (hj : (j : ℕ) < k) (hi : k ≤ (i : ℕ)) :
    uMat (extLow B) i j = 0 := by
  rw [uMat_apply, if_neg (fun h => by subst h; omega), dif_neg (fun h => by rw [Fin.lt_def] at h; omega)]

theorem uMat_extLow_inv_apply_of_lt (i j : Fin n) (hj : (j : ℕ) < k) (hi : k ≤ (i : ℕ)) :
    (((uGL (extLow B))⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]) i j = 0 := by
  letI : Invertible (uMat (extLow B)) := Units.invertible (uGL (extLow B))
  have hT : (uMat (extLow B)).BlockTriangular (fun c : Fin n => if (c : ℕ) < k then 0 else 1) := by
    intro a b hab
    by_cases ha : (a : ℕ) < k
    · simp only [ha, if_true] at hab
      split_ifs at hab <;> omega
    · by_cases hb : (b : ℕ) < k
      · exact uMat_extLow_apply_of_lt B a b hb (by omega)
      · simp only [ha, hb, if_false] at hab
        omega
  have hTi := Matrix.blockTriangular_inv_of_blockTriangular hT
  rw [Matrix.coe_units_inv, coe_uGL]
  exact hTi (by simp only; rw [if_pos hj, if_neg (by omega)]; norm_num)

theorem blockEntry_mul_vanishing {M : Matrix (Fin n) (Fin n) 𝔸[K]}
    (hM : ∀ i j : Fin n, (j : ℕ) < k → k ≤ (i : ℕ) → M i j = 0) (A : UPos n k → 𝔸[K]) :
    ∀ i j : Fin n, ¬ ((i : ℕ) < k ∧ k ≤ (j : ℕ)) → (blockEntry A * M) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [blockEntry_apply]
  split_ifs with h
  · rw [hM c j (by omega) h.2, mul_zero]
  · rw [zero_mul]

def shear : (UPos n k → 𝔸[K]) ≃+ (UPos n k → 𝔸[K]) where
  toFun A u := (blockEntry A * uMat (extLow B)) u.1.1 u.1.2
  invFun Z u := (blockEntry Z * (((uGL (extLow B))⁻¹ : GL (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) 𝔸[K])) u.1.1 u.1.2
  left_inv A := by
    funext u
    simp only
    rw [blockEntry_eq_of_vanishing (blockEntry_mul_vanishing (uMat_extLow_apply_of_lt B) A),
      Matrix.mul_assoc, ← coe_uGL, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
      blockEntry_apply, dif_pos u.2]
  right_inv Z := by
    funext u
    simp only
    rw [blockEntry_eq_of_vanishing (blockEntry_mul_vanishing (uMat_extLow_inv_apply_of_lt B) Z),
      Matrix.mul_assoc, ← coe_uGL, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
      blockEntry_apply, dif_pos u.2]
  map_add' A A' := by
    funext u
    simp [blockEntry_add, Matrix.add_mul]

end Shear

section Shear2

variable {k : ℕ} (B : LowPos n k → 𝔸[K])

theorem unipMatrix_mul_uMat_extLow (A : UPos n k → 𝔸[K]) :
    unipMatrix A * uMat (extLow B) = uMat (extLow B + extU (shear B A)) := by
  rw [unipMatrix, Matrix.add_mul, Matrix.one_mul]
  ext i j
  have hv := blockEntry_mul_vanishing (uMat_extLow_apply_of_lt B) A i j
  rw [Matrix.add_apply, uMat_apply, uMat_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, hv (by omega), add_zero]
  · rw [if_neg hij, if_neg hij]
    by_cases hlt : i < j
    · rw [dif_pos hlt, dif_pos hlt, Pi.add_apply, extU]
      congr 1
      split_ifs with h
      · rfl
      · exact hv h
    · rw [dif_neg hlt, dif_neg hlt, zero_add]
      exact hv (fun h => hlt (by rw [Fin.lt_def]; omega))

theorem continuous_blockEntry :
    Continuous (blockEntry (n := n) (r := k) (R := 𝔸[K])) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [blockEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_shear : Continuous (shear B) :=
  continuous_pi fun u => (continuous_apply u.1.2).comp ((continuous_apply u.1.1).comp
    (continuous_blockEntry.matrix_mul continuous_const))

theorem continuous_shear_symm : Continuous (shear B).symm :=
  continuous_pi fun u => (continuous_apply u.1.2).comp ((continuous_apply u.1.1).comp
    (continuous_blockEntry.matrix_mul continuous_const))

theorem isAddFundamentalDomain_shear_symm :
    IsAddFundamentalDomain (vecLattice K (UPos n k)) ((shear B).symm '' vecDomain K (UPos n k))
      (vecMeasure K (UPos n k)) := by
  classical
  have himg : (shear B).symm '' vecDomain K (UPos n k) = (shear B) ⁻¹' vecDomain K (UPos n k) := by
    ext A
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      simpa using hZ
    · intro h
      exact ⟨shear B A, h, by simp⟩
  rw [himg]
  refine IsAddFundamentalDomain.mk' ((measurableSet_vecDomain.preimage
    (continuous_shear B).measurable).nullMeasurableSet) fun y => ?_
  refine existsUnique_triangular (fun u : UPos n k => u.1.2.val)
    (fun u z => ∑ c ∈ Finset.univ.erase u.1.2, blockEntry z u.1.1 c * uMat (extLow B) c u.1.2)
    (fun z u => ?_) (fun u z z' hzz' => ?_) y
  · show (blockEntry z * uMat (extLow B)) u.1.1 u.1.2 = _
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ u.1.2), blockEntry_apply,
      dif_pos u.2, uMat_apply, if_pos rfl, mul_one]
  · refine Finset.sum_congr rfl fun c hc => ?_
    by_cases hcu : c < u.1.2
    · rw [blockEntry_apply, blockEntry_apply]
      split_ifs with h
      · rw [hzz' ⟨(u.1.1, c), h⟩ (by rw [Fin.lt_def] at hcu; exact hcu)]
      · rfl
    · have hne : c ≠ u.1.2 := Finset.ne_of_mem_erase hc
      have : uMat (extLow B) c u.1.2 = 0 := by
        rw [uMat_apply, if_neg hne, dif_neg (fun h => hcu (by
          rw [Fin.lt_def] at h ⊢; have := Fin.val_injective.ne hne; omega))]
      rw [this, mul_zero, mul_zero]

theorem setIntegral_uGL_extLow_extU {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsLeftInvariant ϕ)
    (g : AdelicGLn.AdelicGL K n) :
    ∫ A in vecDomain K (UPos n k), ϕ (uGL (extLow B + extU A) * g) ∂vecMeasure K (UPos n k) =
      constantTerm k ϕ (uGL (extLow B) * g) := by
  have hrepr : ∀ A, uGL (extLow B + extU A) = unipGL ((shear B).symm A) * uGL (extLow B) := by
    intro A
    refine Units.ext ?_
    rw [Units.val_mul, coe_unipGL, coe_uGL, coe_uGL, unipMatrix_mul_uMat_extLow,
      AddEquiv.apply_symm_apply]
  simp_rw [hrepr, mul_assoc]
  rw [setIntegral_comp_addEquiv (shear B).symm (continuous_shear_symm B) (continuous_shear B)
    (isAddFundamentalDomain_shear_symm B) (f := fun A => ϕ (unipGL A * (uGL (extLow B) * g)))
    fun ξ hξ x => hϕ.unipGL_vadd _ ⟨ξ, hξ⟩ x]
  rfl

end Shear2

theorem vecCoeff_zero_of_isCuspidal {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n) :
    vecCoeff (fun x => partialCoeff ϕ (k + 1) (colGL k x * g)) 0 = 0 := by
  rw [vecCoeff_zero_eq_setIntegral_low hc hk g]
  refine (setIntegral_congr_fun measurableSet_vecDomain fun B _ => ?_).trans (integral_zero _ _)
  rw [setIntegral_uGL_extLow_extU B hl g, hcusp k hk0 hk, mul_zero]

end FourierWhittaker

end

end GroundTheory.Automorphic
