import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC

noncomputable section

open Matrix Polynomial ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped Classical

namespace GlobalTheory.CentValHom

theorem eq_diagonal_of_commute {F : Type*} [Field F] {n : ℕ} (lam : Fin n → F)
    (hlam : Function.Injective lam) (W : Matrix (Fin n) (Fin n) F)
    (h : W * diagonal lam = diagonal lam * W) : W = diagonal (fun i => W i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.2 (fun e => hij (hlam e).symm)
    have h2 : W i j * (lam j - lam i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right hne

theorem exists_eigenbasis {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (lam : Fin n → F)
    (hlam : Function.Injective lam) (hroot : ∀ j, A.charpoly.IsRoot (lam j)) :
    ∃ U : Matrix (Fin n) (Fin n) F, IsUnit U.det ∧ A * U = U * diagonal lam := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' A) (lam j) := fun j =>
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact hroot j)
  choose u hu using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent F u := Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) lam hlam u hu
  refine ⟨Matrix.of fun i j => u j i, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  · ext i j
    have h1 := congrFun ((hu j).apply_eq_smul) i
    rw [Matrix.toLin'_apply] at h1
    rw [mul_diagonal]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, mul_comm]

theorem exists_valHom_bounded_ker (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hL : FiniteDimensional ℚ_[p] L) (n : ℕ) (N : GL (Fin n) L) (hsep : N.val.charpoly.Separable) :
    ∃ (v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ)) (c : ℝ),
      ∀ z : Subgroup.centralizer {N}, v z = 1 → ∀ i j,
        ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c := by
  set φ : L →+* PadicAlgCl p := algebraMap L (PadicAlgCl p) with hφ
  set χ := N.val.charpoly with hχ
  have hsep' : (χ.map φ).Separable := hsep.map
  set s : Finset (PadicAlgCl p) := (χ.map φ).roots.toFinset with hs_def
  have hs : s.card = n := by
    rw [hs_def, Multiset.toFinset_card_of_nodup (nodup_roots hsep'), IsAlgClosed.card_roots_eq_natDegree,
      natDegree_map, hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    L ⊔ IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p)) with hE_def
  have hE : FiniteDimensional ℚ_[p] E := by
    have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    infer_instance
  have hLE : L ≤ E := le_sup_left
  set ι : L →+* E := (IntermediateField.inclusion hLE).toRingHom with hι
  have hιφ : ((E.val : E →ₐ[ℚ_[p]] PadicAlgCl p) : E →+* PadicAlgCl p).comp ι = φ := by
    ext x; rfl
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  have hmem : ∀ j, ((e j : PadicAlgCl p)) ∈ E := fun j =>
    (le_sup_right : IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p)) ≤ E)
      (IntermediateField.subset_adjoin _ _ (e j).2)
  let lam : Fin n → E := fun j => ⟨e j, hmem j⟩
  have hlam : Function.Injective lam := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact e.injective (Subtype.ext h1)
  set A : Matrix (Fin n) (Fin n) E := N.val.map ι with hA
  have hroot : ∀ j, A.charpoly.IsRoot (lam j) := by
    intro j
    have h1 : (χ.map φ).IsRoot (e j : PadicAlgCl p) := by
      have h2 : ((e j : s) : PadicAlgCl p) ∈ (χ.map φ).roots.toFinset := (e j).2
      rw [Multiset.mem_toFinset] at h2
      exact (mem_roots hsep'.ne_zero).1 h2
    rw [hA, Matrix.charpoly_map, IsRoot.def]
    apply Subtype.val_injective
    have h3 : (((χ.map ι).eval (lam j) : E) : PadicAlgCl p) =
        ((E.val : E →ₐ[ℚ_[p]] PadicAlgCl p) : E →+* PadicAlgCl p) ((χ.map ι).eval (lam j)) := rfl
    rw [h3, eval_map, hom_eval₂, hιφ, ← eval_map]
    exact h1
  obtain ⟨U, hU, hAU⟩ := exists_eigenbasis A lam hlam hroot
  have hD : diagonal lam = U⁻¹ * A * U := by
    rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

  let W : Subgroup.centralizer {N} → Matrix (Fin n) (Fin n) E :=
    fun z => U⁻¹ * ((z : GL (Fin n) L).val.map ι) * U
  have hcomm : ∀ z : Subgroup.centralizer {N},
      ((z : GL (Fin n) L).val.map ι) * A = A * ((z : GL (Fin n) L).val.map ι) := by
    intro z
    have h1 := Subgroup.mem_centralizer_iff.1 z.2 N (Set.mem_singleton N)
    have h2 : N.val * (z : GL (Fin n) L).val = (z : GL (Fin n) L).val * N.val := by
      rw [← Units.val_mul, ← Units.val_mul, h1]
    rw [hA, ← Matrix.map_mul, ← Matrix.map_mul, h2]
  have hdiag : ∀ z, W z = diagonal (fun i => W z i i) := by
    intro z
    apply eq_diagonal_of_commute lam hlam
    rw [hD]
    simp only [W, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hU, Matrix.mul_nonsing_inv_cancel_left _ _ hU,
      ← Matrix.mul_assoc _ A U, hcomm z, Matrix.mul_assoc]
  have hW1 : W 1 = 1 := by
    simp only [W, OneMemClass.coe_one, Units.val_one]
    rw [Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.mul_one, Matrix.nonsing_inv_mul _ hU]
  have hWmul : ∀ z w, W (z * w) = W z * W w := by
    intro z w
    have h1 : ((z * w : Subgroup.centralizer {N}) : GL (Fin n) L).val =
        (z : GL (Fin n) L).val * (w : GL (Fin n) L).val := rfl
    show U⁻¹ * (((z * w : Subgroup.centralizer {N}) : GL (Fin n) L).val.map ι) * U =
      (U⁻¹ * ((z : GL (Fin n) L).val.map ι) * U) * (U⁻¹ * ((w : GL (Fin n) L).val.map ι) * U)
    rw [h1, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hU]
  let μ : Fin n → (Subgroup.centralizer {N} →* E) := fun j =>
    { toFun := fun z => W z j j
      map_one' := by simp only [hW1, Matrix.one_apply_eq]
      map_mul' := fun z w => by
        show W (z * w) j j = W z j j * W w j j
        rw [hWmul]
        conv_lhs => rw [hdiag z, hdiag w]
        rw [diagonal_mul_diagonal, diagonal_apply_eq] }
  let μu : Fin n → (Subgroup.centralizer {N} →* Eˣ) := fun j => (μ j).toHomUnits
  let v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ) :=
    { toFun := fun z => Multiplicative.ofAdd (fun j => vK p E (μu j z))
      map_one' := by
        simp only [map_one, vK_one]
        rfl
      map_mul' := fun z w => by
        simp only [map_mul, vK_mul]
        rfl }
  refine ⟨v, ∑ i, ∑ k, ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ * ‖((U⁻¹ j k : E) : PadicAlgCl p)‖, ?_⟩
  intro z hz i k
  have hv0 : ∀ j, vK p E (μu j z) = 0 := by
    intro j
    have h1 : (fun j => vK p E (μu j z)) = 0 := ofAdd_eq_one.1 hz
    exact congrFun h1 j
  have hnorm : ∀ j, ‖((W z j j : E) : PadicAlgCl p)‖ = 1 := fun j =>
    (mem_UK_iff p E hE (μu j z)).2 (hv0 j)
  have hz' : (z : GL (Fin n) L).val.map ι = U * diagonal (fun j => W z j j) * U⁻¹ := by
    rw [← hdiag z]
    simp only [W, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hU, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hU]
  have hent : ((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i k : L) : PadicAlgCl p) =
      ((((z : GL (Fin n) L).val.map ι) i k : E) : PadicAlgCl p) := rfl
  rw [hent, hz']
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, IntermediateField.coe_sum, IntermediateField.coe_mul]
  calc _ ≤ ∑ j, ‖((U i j : E) : PadicAlgCl p) * ((W z j j : E) : PadicAlgCl p) *
          ((U⁻¹ j k : E) : PadicAlgCl p)‖ := norm_sum_le _ _
    _ = ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ * ‖((U⁻¹ j k : E) : PadicAlgCl p)‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, norm_mul, hnorm j, mul_one]
    _ ≤ ∑ k', ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ * ‖((U⁻¹ j k' : E) : PadicAlgCl p)‖ :=
        Finset.single_le_sum (f := fun k' => ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ *
          ‖((U⁻¹ j k' : E) : PadicAlgCl p)‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (Finset.mem_univ k)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun i' => ∑ k', ∑ j, ‖((U i' j : E) : PadicAlgCl p)‖ *
          ‖((U⁻¹ j k' : E) : PadicAlgCl p)‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (Finset.mem_univ i)

theorem centralizer_valHom_bounded_ker : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (N : GL (Fin n) L), N.val.charpoly.Separable →
    ∃ (v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ)) (c : ℝ),
      ∀ z : Subgroup.centralizer {N}, v z = 1 → ∀ i j,
        ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c :=
  fun p _ L hL n N hsep => exists_valHom_bounded_ker p L hL n N hsep

end GlobalTheory.CentValHom
