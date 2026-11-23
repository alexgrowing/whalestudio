import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

variable {p q : ℕ}

def vecM (V : Mat p q) : Ix p q × Ix p q → ℂ := fun ab => V ab.1 ab.2

def sAd (Y V : Mat p q) : Mat p q := Matrix.of fun a b => (sinhcAd Y *ᵥ vecM V) (a, b)

def pY (B : Fin p → Fin q → ℂ) : Mat p q := pOf (Matrix.of B)

theorem pY_add (B C : Fin p → Fin q → ℂ) : pY (B + C) = pY B + pY C := by
  ext (i | i) (j | j) <;> simp [pY, pOf]

theorem pY_smul (t : ℝ) (B : Fin p → Fin q → ℂ) : pY (t • B) = t • pY B := by
  ext (i | i) (j | j) <;> simp [pY, pOf, Complex.real_smul, mul_comm]

theorem continuous_pY : Continuous (pY : (Fin p → Fin q → ℂ) → Mat p q) := by
  show Continuous fun B : Fin p → Fin q → ℂ => Matrix.fromBlocks 0 (Matrix.of B) (Matrix.of B)ᴴ 0
  refine continuous_pi fun a => continuous_pi fun b => ?_
  rcases a with a | a <;> rcases b with b | b <;> simp <;> fun_prop

theorem sAd_add (Y V W : Mat p q) : sAd Y (V + W) = sAd Y V + sAd Y W := by
  have h : vecM (V + W) = vecM V + vecM W := rfl
  ext a b
  simp [sAd, h, Matrix.mulVec_add]

theorem sAd_smul_real (Y V : Mat p q) (t : ℝ) : sAd Y (t • V) = t • sAd Y V := by
  have h : vecM (t • V) = (t : ℂ) • vecM V := by
    funext ab
    simp [vecM, Complex.real_smul]
  ext a b
  simp [sAd, h, Matrix.mulVec_smul, Complex.real_smul]

def sP (Y : Mat p q) : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ) where
  toFun B := fun i j => sAd Y (pY B) (Sum.inl i) (Sum.inr j)
  map_add' B C := by funext i j; simp [pY_add, sAd_add]
  map_smul' t B := by funext i j; simp [pY_smul, sAd_smul_real]

theorem adMat_mulVec (Y V : Mat p q) : adMat Y *ᵥ vecM V = vecM (Y * V - V * Y) := by
  funext ⟨a, b⟩
  have h1 : (Matrix.kroneckerMap (· * ·) Y (1 : Mat p q) *ᵥ vecM V) (a, b) = (Y * V) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, ite_mul]
  have h2 : (Matrix.kroneckerMap (· * ·) (1 : Mat p q) Yᵀ *ᵥ vecM V) (a, b) = (V * Y) a b := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right, Matrix.one_apply, Matrix.mul_apply,
      vecM, mul_ite, mul_comm]
  simp only [adMat, Matrix.sub_mulVec, Pi.sub_apply, h1, h2, vecM, Matrix.sub_apply]

theorem pY_conjTranspose (B : Fin p → Fin q → ℂ) : (pY B)ᴴ = pY B := by
  simp [pY, pOf, Matrix.fromBlocks_conjTranspose]

theorem pY_mem (B : Fin p → Fin q → ℂ) : pY B ∈ pR p q := by
  show pY B ∈ upq p q ∧ IsPC (pY B)
  refine ⟨?_, ?_⟩
  · show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
    rw [pY_conjTranspose]
    simp [pY, pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [pY, pOf, sameBlock]

theorem exists_pY {Y : Mat p q} (hY : Y ∈ pR p q) : ∃ B, Y = pY B := by
  have hY' : Y ∈ upq p q ∧ IsPC Y := hY
  obtain ⟨hu, hP⟩ := hY'
  have hu' : Yᴴ * Jm p q + Jm p q * Y = 0 := hu
  refine ⟨Y.toBlocks₁₂, ?_⟩
  ext (i | i) (j | j)
  · simpa [pY, pOf] using hP (Sum.inl i) (Sum.inl j) (by simp [sameBlock])
  · rfl
  · have h := congrFun (congrFun hu' (Sum.inr i)) (Sum.inl j)
    simp [Matrix.mul_apply, Jm, Formalism.UG.Jpq, Fintype.sum_sum_type, Matrix.one_apply, mul_ite,
      ite_mul] at h
    rw [starRingEnd_apply] at h
    show Y (Sum.inr i) (Sum.inl j) = star (Y (Sum.inl j) (Sum.inr i))
    linear_combination -h
  · simpa [pY, pOf] using hP (Sum.inr i) (Sum.inr j) (by simp [sameBlock])

def posIx : Ix p q → ℕ := Sum.elim (fun i => i.val) (fun j => j.val)

def cutH (p q : ℕ) (h : ℕ → ℝ) (n : ℕ) : ℝ := if n < min p q then h n else 0

def rootP (h : ℕ → ℝ) (ab : Ix p q × Ix p q) : ℝ :=
  if ab.1.isLeft then cutH p q h (posIx ab.1) - cutH p q h (posIx ab.2)
  else cutH p q h (posIx ab.1) + cutH p q h (posIx ab.2)

def eigP (ab cd : Ix p q × Ix p q) : ℂ :=
  if cd = ab then 1
  else if ¬ sameBlock cd.1 cd.2 ∧ posIx cd.1 = posIx ab.1 ∧ posIx cd.2 = posIx ab.2 then
    (if ab.1.isLeft then 1 else -1)
  else 0

theorem eigenvectorMatrix_eq_zero_of_sameBlock (ab : PIx p q) (cd : Ix p q × Ix p q) (h : sameBlock cd.1 cd.2) :
    eigP ab.1 cd = 0 := by
  have hne : cd ≠ ab.1 := by
    rintro rfl
    exact ab.2 h
  simp [eigP, hne, h]

def matG (T : GrpData p q) (x : T.G) : Mat p q := ((T.cov x : GL (Ix p q) ℂ) : Mat p q)

theorem matG_mul (T : GrpData p q) (x y : T.G) : matG T (x * y) = matG T x * matG T y := by
  simp only [matG, map_mul, Units.val_mul]

theorem matG_expt (T : GrpData p q) (B : Fin p → Fin q → ℂ) :
    matG T (T.expt (pY B)) = NormedSpace.exp (pY B) := by
  exact T.expt_cov (pY B) (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1

theorem continuous_expt_pY (T : GrpData p q) :
    Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) := by
  exact T.expt_cont.comp_continuous continuous_pY
    (fun B => (show pY B ∈ upq p q ∧ IsPC (pY B) from pY_mem B).1)

theorem continuous_matG (T : GrpData p q) : Continuous (matG T) := by
  show Continuous fun x => ((T.cov x : GL (Ix p q) ℂ) : Mat p q)
  exact Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)

theorem matG_J (T : GrpData p q) (x : T.G) : (matG T x)ᴴ * Jm p q * matG T x = Jm p q := by
  have h : Formalism.UG.cT (starRingEnd ℂ) (matG T x) * Formalism.UG.Jpq p q * matG T x = Formalism.UG.Jpq p q :=
    T.cov_mem x
  have hc : Formalism.UG.cT (starRingEnd ℂ) (matG T x) = (matG T x)ᴴ := by
    ext i j
    simp [Formalism.UG.cT]
  rw [hc] at h
  exact h

theorem matG_one (T : GrpData p q) : matG T 1 = 1 := by
  simp [matG]

theorem matG_inv (T : GrpData p q) (x : T.G) :
    matG T x⁻¹ = (((T.cov x)⁻¹ : GL (Ix p q) ℂ) : Mat p q) := by
  simp only [matG, map_inv]

theorem exists_blocks (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      matG T k = Matrix.fromBlocks U 0 0 V := by
  have hK : IsKC (matG T k) := hk
  have h12 : (matG T k).toBlocks₁₂ = 0 := by
    ext i j
    exact hK (Sum.inl i) (Sum.inr j) (by simp [sameBlock])
  have h21 : (matG T k).toBlocks₂₁ = 0 := by
    ext i j
    exact hK (Sum.inr i) (Sum.inl j) (by simp [sameBlock])
  have hMe : matG T k = Matrix.fromBlocks (matG T k).toBlocks₁₁ 0 0 (matG T k).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (matG T k)]
    rw [h12, h21]
  have hJ := matG_J T k
  rw [hMe] at hJ
  generalize (matG T k).toBlocks₁₁ = A at hJ hMe
  generalize (matG T k).toBlocks₂₂ = D at hJ hMe
  simp only [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hJ
  simp [Matrix.fromBlocks_inj] at hJ
  obtain ⟨hA, hD⟩ := hJ
  refine ⟨A, ?_, D, ?_, hMe⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hA
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hD

theorem matG_star_mul (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    (matG T k)ᴴ * matG T k = 1 := by
  obtain ⟨U, hU, V, hV, h⟩ := exists_blocks T hk
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [h, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

theorem matG_inv_of_mem (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    matG T k⁻¹ = (matG T k)ᴴ := by
  rw [matG_inv]
  exact Units.inv_eq_of_mul_eq_one_left (matG_star_mul T hk)

def Ksub (T : GrpData p q) : Subgroup T.G where
  carrier := T.Kset
  one_mem' := by
    show IsKC (matG T 1)
    rw [matG_one]; intro a b h
    have : a ≠ b := by rintro rfl; cases a <;> simp [sameBlock] at h
    simp [Matrix.one_apply, this]
  mul_mem' := by
    intro x y hx hy
    obtain ⟨U, -, V, -, h⟩ := exists_blocks T hx
    obtain ⟨U', -, V', -, h'⟩ := exists_blocks T hy
    show IsKC (matG T (x * y))
    rw [matG_mul, h, h', Matrix.fromBlocks_multiply]
    intro a b hab
    cases a <;> cases b <;> simp_all [sameBlock]
  inv_mem' := by
    intro x hx
    show IsKC (matG T x⁻¹)
    rw [matG_inv_of_mem T hx]
    have hx' : IsKC (matG T x) := hx
    intro a b hab
    have : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [hx' b a this]

end GlobalTheory.PolarU
