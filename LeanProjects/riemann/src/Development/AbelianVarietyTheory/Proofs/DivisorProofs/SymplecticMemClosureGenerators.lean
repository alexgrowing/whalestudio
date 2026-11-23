import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SympGen

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev J (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] : Matrix (κ ⊕ κ) (κ ⊕ κ) F :=
  Matrix.fromBlocks 0 1 (-1) 0

def Sp (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop := gᵀ * J F κ * g = J F κ

theorem J_mul_J : J F κ * J F κ = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [J, Matrix.fromBlocks_multiply]

def sInv (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Matrix (κ ⊕ κ) (κ ⊕ κ) F := -(J F κ * gᵀ * J F κ)

theorem sInv_mul {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) : sInv g * g = 1 := by
  have h : J F κ * gᵀ * J F κ * g = J F κ * (gᵀ * J F κ * g) := by simp only [Matrix.mul_assoc]
  rw [sInv, Matrix.neg_mul, h, hg, J_mul_J, neg_neg]

theorem mul_sInv {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) : g * sInv g = 1 :=
  mul_eq_one_comm.mp (sInv_mul hg)

theorem Sp.mul {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) (hh : Sp h) : Sp (g * h) := by
  unfold Sp at *
  rw [Matrix.transpose_mul]
  calc hᵀ * gᵀ * J F κ * (g * h) = hᵀ * (gᵀ * J F κ * g) * h := by simp only [Matrix.mul_assoc]
    _ = J F κ := by rw [hg]; exact hh

theorem Sp.of_mul_eq_one {g s : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) (h1 : g * s = 1) : Sp s := by
  unfold Sp at *
  calc sᵀ * J F κ * s = sᵀ * (gᵀ * J F κ * g) * s := by rw [hg]
    _ = (g * s)ᵀ * J F κ * (g * s) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = J F κ := by rw [h1]; simp

theorem Sp.sInv {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : Sp g) : Sp (sInv g) :=
  Sp.of_mul_eq_one hg (mul_sInv hg)

theorem sp_of_mem_gens {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ GlobalTheory.AdelicSvN.gens F κ) : Sp g := by
  rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hw
  · have h1 : Aᵀ * A⁻¹ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hA, Matrix.transpose_one]
    have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
    simp [Sp, J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h1, h2]
  · simp [Sp, J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hC]
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    simp [Sp, J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

theorem sp_of_mem_closure {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ)) : Sp g := by
  induction hg using Submonoid.closure_induction with
  | mem x hx => exact sp_of_mem_gens hx
  | one => simp [Sp]
  | mul x y _ _ hx hy => exact hx.mul hy

private theorem full_of_depthZeroLabels_of_one_le_d {a b c d : Matrix κ κ F} (h : Sp (Matrix.fromBlocks a b c d)) :
    aᵀ * c = cᵀ * a ∧ aᵀ * d - cᵀ * b = 1 ∧ bᵀ * d = dᵀ * b := by
  have e : (Matrix.fromBlocks a b c d)ᵀ * J F κ * Matrix.fromBlocks a b c d =
      Matrix.fromBlocks (aᵀ * c - cᵀ * a) (aᵀ * d - cᵀ * b) (bᵀ * c - dᵀ * a) (bᵀ * d - dᵀ * b) := by
    simp [J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, sub_eq_add_neg, add_comm]
  unfold Sp at h
  rw [e] at h
  obtain ⟨h1, h2, -, h4⟩ := Matrix.fromBlocks_inj.mp h
  exact ⟨sub_eq_zero.mp h1, h2, sub_eq_zero.mp h4⟩

end GlobalTheory.SympGen

namespace GlobalTheory.SympGen

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem mem_closure_of_lower {k : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hk : Sp k) (h12 : k.toBlocks₁₂ = 0) :
    k ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  obtain ⟨A, B, c, D, rfl⟩ : ∃ A B c D, k = Matrix.fromBlocks A B c D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks k).symm⟩
  simp only [Matrix.toBlocks_fromBlocks₁₂] at h12
  subst h12
  obtain ⟨hc, hAD, -⟩ := full_of_depthZeroLabels_of_one_le_d hk
  simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_zero] at hAD
  have hdet : IsUnit A.det := by
    have := congrArg Matrix.det hAD
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ this
  have hD : D = A⁻¹ᵀ := by
    rw [Matrix.transpose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv hAD).symm
  subst hD
  have hAA : A⁻¹ᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv A hdet, Matrix.transpose_one]
  have hsym : (-(Aᵀ * c))ᵀ = -(Aᵀ * c) := by
    rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_transpose, hc]
  have e : Matrix.fromBlocks A 0 c A⁻¹ᵀ =
      Matrix.fromBlocks A 0 0 A⁻¹ᵀ * Matrix.fromBlocks 1 0 (-(-(Aᵀ * c))) 1 := by
    simp [Matrix.fromBlocks_multiply, ← Matrix.mul_assoc, hAA]
  rw [e]
  refine Submonoid.mul_mem _ (Submonoid.subset_closure ?_) (Submonoid.subset_closure ?_)
  · exact Or.inl (Or.inl ⟨A, hdet, rfl⟩)
  · exact Or.inl (Or.inr ⟨-(Aᵀ * c), hsym, rfl⟩)

def vert : (κ → F) →ₗ[F] (κ ⊕ κ → F) where
  toFun y := Sum.elim 0 y
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

def halves : (κ ⊕ κ → F) →ₗ[F] (κ → F) × (κ → F) :=
  LinearMap.prod (LinearMap.funLeft F F Sum.inl) (LinearMap.funLeft F F Sum.inr)

private theorem exists_symm_isUnit_det_sub_mul_of_finrank_ker (b : Matrix κ κ F) :
    ∀ (n : ℕ) (d : Matrix κ κ F), Module.finrank F (LinearMap.ker d.mulVecLin) = n →
      bᵀ * d = dᵀ * b → (∀ x, b *ᵥ x = 0 → d *ᵥ x = 0 → x = 0) →
        ∃ C : Matrix κ κ F, Cᵀ = C ∧ IsUnit (d - C * b).det := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hn hbd hinj
  by_cases hd : LinearMap.ker d.mulVecLin = ⊥
  · refine ⟨0, by simp, ?_⟩
    rw [Matrix.zero_mul, sub_zero, ← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hd)
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hd
  have hdx : d *ᵥ x = 0 := by simpa using hxk
  have hbx : b *ᵥ x ≠ 0 := fun h0 => hx0 (hinj x h0 hdx)
  obtain ⟨i, hi⟩ : ∃ i, (b *ᵥ x) i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hbx (funext hc)
  have key : ∀ y, (b *ᵥ x) ⬝ᵥ (d *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hbd,
      ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hdx, Matrix.zero_vecMul, zero_dotProduct]
  set E : Matrix κ κ F := Matrix.diagonal (Pi.single i 1) with hEdef
  have hE : ∀ w : κ → F, E *ᵥ w = Pi.single i (w i) := by
    intro w
    funext j
    rw [hEdef, Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  have hET : Eᵀ = E := by rw [hEdef, Matrix.diagonal_transpose]
  set d' := d - E * b with hd'
  have hd'v : ∀ y, d' *ᵥ y = d *ᵥ y - Pi.single i ((b *ᵥ y) i) := by
    intro y
    rw [hd', Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hE]
  have hbd' : bᵀ * d' = d'ᵀ * b := by
    rw [hd', Matrix.transpose_sub, Matrix.transpose_mul, hET, Matrix.mul_sub, Matrix.sub_mul, hbd,
      Matrix.mul_assoc]
  have hsub : ∀ y, d' *ᵥ y = 0 → d *ᵥ y = 0 := by
    intro y hy
    rw [hd'v, sub_eq_zero] at hy
    have h1 := key y
    rw [hy, dotProduct_single] at h1
    have h2 : (b *ᵥ y) i = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hi
      · exact h
    rw [hy, h2, Pi.single_zero]
  have hinj' : ∀ y, b *ᵥ y = 0 → d' *ᵥ y = 0 → y = 0 :=
    fun y hb hy => hinj y hb (hsub y hy)
  have hlt : LinearMap.ker d'.mulVecLin < LinearMap.ker d.mulVecLin := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun y hy => ?_, x, hxk, fun hx' => ?_⟩
    · simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
      exact hsub y hy
    · simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx'
      rw [hd'v, hdx, zero_sub, neg_eq_zero] at hx'
      have := congrFun hx' i
      simp only [Pi.single_eq_same, Pi.zero_apply] at this
      exact hi this
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hn] at hlt'
  obtain ⟨C, hC, hu⟩ := ih _ hlt' d' rfl hbd' hinj'
  refine ⟨C + E, by rw [Matrix.transpose_add, hC, hET], ?_⟩
  have : d - (C + E) * b = d' - C * b := by
    rw [hd', Matrix.add_mul]; abel
  rw [this]
  exact hu

private theorem fromBlocks_one_symm_mem_closure_gens (T : Matrix κ κ F) (hT : Tᵀ = T) :
    Matrix.fromBlocks 1 T 0 1 ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  have hw : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) ∈
      Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) :=
    Submonoid.subset_closure (Or.inr rfl)
  have hu : (Matrix.fromBlocks 1 0 (-T) 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) ∈
      Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) :=
    Submonoid.subset_closure (Or.inl (Or.inr ⟨T, hT, rfl⟩))
  have e : (Matrix.fromBlocks 1 T 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) =
      Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 (-T) 1 *
        (Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 0 1 (-1) 0) := by
    simp [Matrix.fromBlocks_multiply]
  rw [e]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hw hu)
    (Submonoid.mul_mem _ (Submonoid.mul_mem _ hw hw) hw)

theorem main (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (hg : Sp g) : g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, g = Matrix.fromBlocks a b c d :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  obtain ⟨-, -, hbd⟩ := full_of_depthZeroLabels_of_one_le_d hg
  have hinj : ∀ x, b *ᵥ x = 0 → d *ᵥ x = 0 → x = 0 := by
    intro x hb hd
    have h1 : Matrix.fromBlocks a b c d *ᵥ (Sum.elim 0 x) = 0 := by
      rw [Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [hb, hd]
    have h2 : Sum.elim (0 : κ → F) x = 0 := by
      have := congrArg (fun v => sInv (Matrix.fromBlocks a b c d) *ᵥ v) h1
      simpa [Matrix.mulVec_mulVec, sInv_mul hg] using this
    funext i
    exact congrFun h2 (Sum.inr i)
  obtain ⟨C, hC, hdu⟩ := exists_symm_isUnit_det_sub_mul_of_finrank_ker b _ d rfl hbd hinj
  set d' := d - C * b with hd'
  have hu : Sp (Matrix.fromBlocks 1 0 (-C) 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
    sp_of_mem_gens (Or.inl (Or.inr ⟨C, hC, rfl⟩))
  have e1 : Matrix.fromBlocks 1 0 (-C) 1 * Matrix.fromBlocks a b c d =
      Matrix.fromBlocks a b (c - C * a) d' := by
    simp [Matrix.fromBlocks_multiply, hd', sub_eq_add_neg, add_comm]
  have hg1 : Sp (Matrix.fromBlocks a b (c - C * a) d') := by
    rw [← e1]; exact hu.mul hg
  obtain ⟨-, -, hbd1⟩ := full_of_depthZeroLabels_of_one_le_d hg1
  have hdu' : IsUnit d'ᵀ.det := by rwa [Matrix.det_transpose]
  set S := b * d'⁻¹ with hSdef
  have hS : Sᵀ = S := by
    calc Sᵀ = d'ᵀ⁻¹ * bᵀ := by rw [hSdef, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      _ = d'ᵀ⁻¹ * (bᵀ * d') * d'⁻¹ := by
        rw [Matrix.mul_assoc _ (bᵀ * d'), Matrix.mul_assoc bᵀ, Matrix.mul_nonsing_inv _ hdu,
          Matrix.mul_one]
      _ = d'ᵀ⁻¹ * d'ᵀ * b * d'⁻¹ := by rw [hbd1]; simp only [Matrix.mul_assoc]
      _ = S := by rw [Matrix.nonsing_inv_mul _ hdu', Matrix.one_mul]
  have hSd : S * d' = b := by
    rw [hSdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdu, Matrix.mul_one]
  set k := Matrix.fromBlocks 1 (-S) 0 1 * Matrix.fromBlocks a b (c - C * a) d' with hk
  have hkSp : Sp k := by
    have hn : Sp (Matrix.fromBlocks 1 (-S) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
      sp_of_mem_closure (fromBlocks_one_symm_mem_closure_gens (-S) (by rw [Matrix.transpose_neg, hS]))
    exact hn.mul hg1
  have hk12 : k.toBlocks₁₂ = 0 := by
    simp [hk, Matrix.fromBlocks_multiply, Matrix.neg_mul, hSd]
  have hkm := mem_closure_of_lower hkSp hk12
  have e2 : Matrix.fromBlocks a b c d =
      Matrix.fromBlocks 1 0 (-(-C)) 1 * (Matrix.fromBlocks 1 S 0 1 * k) := by
    rw [hk, ← Matrix.mul_assoc (Matrix.fromBlocks 1 S 0 1), ← e1]
    simp [Matrix.fromBlocks_multiply]
  rw [e2]
  refine Submonoid.mul_mem _ (Submonoid.subset_closure ?_) (Submonoid.mul_mem _ (fromBlocks_one_symm_mem_closure_gens S hS) hkm)
  exact Or.inl (Or.inr ⟨-C, by rw [Matrix.transpose_neg, hC], rfl⟩)

end GlobalTheory.SympGen

theorem GlobalTheory.sympGen : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F),
    gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 →
      g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) := by
  intro F _ κ _ _ g hg
  exact GlobalTheory.SympGen.main g hg
