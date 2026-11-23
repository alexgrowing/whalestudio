import Mathlib
import GroundTheory.AutomorphicForms.AdmissibleInduction
import GroundTheory.AutomorphicForms.CuspidalAdmissible
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal

section LeviPar

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')

abbrev LeviParIndex : Type := {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ ¬ δ ij.2 < δ ij.1}

def lieLeviPar : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, ¬ (γ i = γ j ∧ ¬ δ j < δ i) → A i j = 0}
  add_mem' {A B} hA hB i j h := by
    simp [hA i j h, hB i j h]
  zero_mem' _ _ _ := rfl
  smul_mem' c A hA i j h := by
    simp [hA i j h]

abbrev leviPar : Subgroup (GL (Fin n) F) := levi F n γ ⊓ blockUpper F n δ

variable {F n γ δ}

theorem mem_lieLeviPar {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLeviPar F n γ δ ↔ ∀ i j, ¬ (γ i = γ j ∧ ¬ δ j < δ i) → A i j = 0 :=
  Iff.rfl

theorem mem_leviPar_iff {g : GL (Fin n) F} :
    g ∈ leviPar F n γ δ ↔ (g : Matrix (Fin n) (Fin n) F) ∈ lieLeviPar F n γ δ := by
  rw [Subgroup.mem_inf, mem_levi, mem_blockUpper]
  constructor
  · rintro ⟨h1, h2⟩ i j h
    by_cases hγ : γ i = γ j
    · exact h2 (by by_contra h'; exact h ⟨hγ, h'⟩)
    · exact h1 i j hγ
  · intro h
    exact ⟨fun i j hij => h i j fun h' => hij h'.1, fun i j hij => h i j fun h' => h'.2 hij⟩

theorem mul_mem_lieLeviPar {A B : Matrix (Fin n) (Fin n) F} (hA : A ∈ lieLeviPar F n γ δ)
    (hB : B ∈ lieLeviPar F n γ δ) : A * B ∈ lieLeviPar F n γ δ := by
  intro i j h
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : γ i = γ k ∧ ¬ δ k < δ i
  · by_cases hkj : γ k = γ j ∧ ¬ δ j < δ k
    · exact absurd ⟨hik.1.trans hkj.1, fun h' => hkj.2 (lt_of_lt_of_le h' (not_lt.1 hik.2))⟩ h
    · rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]

variable (F n γ δ)

noncomputable def leviParCoord : lieLeviPar F n γ δ ≃ₗ[F] (LeviParIndex n γ δ → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : γ i = γ j ∧ ¬ δ j < δ i then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by
      simp only [Matrix.of_apply]
      rw [dif_neg hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : γ i = γ j ∧ ¬ δ j < δ i
    · simp [h]
    · simp [A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]

noncomputable def leviParCoordHomeomorph : lieLeviPar F n γ δ ≃ₜ (LeviParIndex n γ δ → F) where
  toEquiv := (leviParCoord F n γ δ).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieLeviPar F n γ δ => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : γ i = γ j ∧ ¬ δ j < δ i
    · simp only [Matrix.of_apply, h, not_false_eq_true, and_self, dite_true]
      exact continuous_apply _
    · simp only [Matrix.of_apply, h, dite_false]
      exact continuous_const

def toLieLeviPar (l : leviPar F n γ δ) : lieLeviPar F n γ δ :=
  ⟨((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), mem_leviPar_iff.1 l.2⟩

theorem isClosed_leviPar : IsClosed (leviPar F n γ δ : Set (GL (Fin n) F)) := isClosed_levi.inter (Measures.isClosed_blockUpper F n δ)

instance locallyCompactSpace_leviPar : LocallyCompactSpace (leviPar F n γ δ) :=
  (isClosed_leviPar F n γ δ).locallyCompactSpace

theorem isOpenEmbedding_toLieLeviPar : IsOpenEmbedding (toLieLeviPar F n γ δ) := by
  have hemb : IsEmbedding (toLieLeviPar F n γ δ) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieLeviPar F n γ δ : Set (Matrix (Fin n) (Fin n) F))
      fun l : leviPar F n γ δ => mem_leviPar_iff.1 l.2
  refine ⟨hemb, ?_⟩
  have : Set.range (toLieLeviPar F n γ δ) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, mem_leviPar_iff.2 ?_⟩, Subtype.ext hu⟩
      rw [hu]
      exact A.2
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val

noncomputable def mulLeftLeviPar (l : leviPar F n γ δ) :
    lieLeviPar F n γ δ ≃ₗ[F] lieLeviPar F n γ δ :=
  (Units.mulLeftLinearEquiv F _ (l : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLeviPar (mem_leviPar_iff.1 l.2) hA
    · refine ⟨((l⁻¹ : leviPar F n γ δ) : GL (Fin n) F) * A,
        mul_mem_lieLeviPar (mem_leviPar_iff.1 (l⁻¹).2) hA, ?_⟩
      simp [← mul_assoc])

noncomputable def mulRightLeviPar (l : leviPar F n γ δ) :
    lieLeviPar F n γ δ ≃ₗ[F] lieLeviPar F n γ δ :=
  (Units.mulRightLinearEquiv F (l : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLeviPar hA (mem_leviPar_iff.1 l.2)
    · refine ⟨A * ((l⁻¹ : leviPar F n γ δ) : GL (Fin n) F),
        mul_mem_lieLeviPar hA (mem_leviPar_iff.1 (l⁻¹).2), ?_⟩
      simp [mul_assoc])

@[simp] theorem coe_mulLeftLeviPar (l : leviPar F n γ δ) (A : lieLeviPar F n γ δ) :
    ((mulLeftLeviPar F n γ δ l A : lieLeviPar F n γ δ) : Matrix (Fin n) (Fin n) F) =
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A :=
  rfl

@[simp] theorem coe_mulRightLeviPar (l : leviPar F n γ δ) (A : lieLeviPar F n γ δ) :
    ((mulRightLeviPar F n γ δ l A : lieLeviPar F n γ δ) : Matrix (Fin n) (Fin n) F) =
      A * ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

noncomputable def adLeviPar (l : leviPar F n γ δ) :
    lieLeviPar F n γ δ ≃ₗ[F] lieLeviPar F n γ δ :=
  (mulLeftLeviPar F n γ δ l).trans (mulRightLeviPar F n γ δ l⁻¹)

@[simp] theorem coe_adLeviPar (l : leviPar F n γ δ) (A : lieLeviPar F n γ δ) :
    ((adLeviPar F n γ δ l A : lieLeviPar F n γ δ) : Matrix (Fin n) (Fin n) F) =
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

noncomputable def leviParChart :
    LinearChart F (LeviParIndex n γ δ) (leviPar F n γ δ) where
  toFun l := leviParCoord F n γ δ (toLieLeviPar F n γ δ l)
  isOpenEmbedding :=
    (leviParCoordHomeomorph F n γ δ).isOpenEmbedding.comp (isOpenEmbedding_toLieLeviPar F n γ δ)
  left l := (leviParCoord F n γ δ).symm.trans ((mulLeftLeviPar F n γ δ l).trans (leviParCoord F n γ δ))
  right l := (leviParCoord F n γ δ).symm.trans
    ((mulRightLeviPar F n γ δ l).trans (leviParCoord F n γ δ))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl

variable {F n γ δ}

theorem leviParChart_leftModulus (l : leviPar F n γ δ) :
    (leviParChart F n γ δ).leftModulus l =
      distribHaarChar F (LinearEquiv.det (mulLeftLeviPar F n γ δ l)) := by
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq]
  congr 1
  exact LinearEquiv.det_conj (mulLeftLeviPar F n γ δ l) (leviParCoord F n γ δ)

theorem leviParChart_rightModulus (l : leviPar F n γ δ) :
    (leviParChart F n γ δ).rightModulus l =
      distribHaarChar F (LinearEquiv.det (mulRightLeviPar F n γ δ l)) := by
  rw [LinearChart.rightModulus, distribHaarChar_pi_eq]
  congr 1
  exact LinearEquiv.det_conj (mulRightLeviPar F n γ δ l) (leviParCoord F n γ δ)

theorem mulRightLeviPar_inv (l : leviPar F n γ δ) :
    mulRightLeviPar F n γ δ l⁻¹ = (mulRightLeviPar F n γ δ l)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext A : 2
  show (A : Matrix (Fin n) (Fin n) F) * ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((l⁻¹ : leviPar F n γ δ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A
  simp [mul_assoc]

theorem modularCharacter_leviPar (l : leviPar F n γ δ) :
    modularCharacter l = distribHaarChar F (LinearEquiv.det (adLeviPar F n γ δ l)) := by
  borelize F ↥(leviPar F n γ δ)
  rw [(leviParChart F n γ δ).modularCharacter_eq l, leviParChart_leftModulus,
    leviParChart_rightModulus]
  have : adLeviPar F n γ δ l = mulRightLeviPar F n γ δ l⁻¹ * mulLeftLeviPar F n γ δ l := rfl
  rw [this, mulRightLeviPar_inv, map_mul, map_inv, map_mul, map_inv, div_eq_mul_inv, mul_comm]

theorem modularCharacter_leviPar_eq_one_of_mem_integralGL (l : leviPar F n γ δ)
    (hl : (l : GL (Fin n) F) ∈ GLnLocal.integralGL F n) : modularCharacter l = 1 := by
  borelize F ↥(leviPar F n γ δ)
  let V : OpenSubgroup (leviPar F n γ δ) :=
    ⟨(GLnLocal.integralGL F n).subgroupOf (leviPar F n γ δ),
      (GLnLocal.isOpen_integralGL F n).preimage continuous_subtype_val⟩
  have hV : IsCompact (V : Set (leviPar F n γ δ)) :=
    (isClosed_leviPar F n γ δ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GLnLocal.isCompact_integralGL F n)
  obtain ⟨h1, h2⟩ := (leviParChart F n γ δ).modulus_eq_one_of_mem hV (v := l) hl
  rw [(leviParChart F n γ δ).modularCharacter_eq, h1, h2, div_one]

end LeviPar

section Diagonal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}

theorem coe_leviParCoord_symm_single (t : LeviParIndex n γ δ) :
    (((leviParCoord F n γ δ).symm (Pi.single t 1) : lieLeviPar F n γ δ) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by
  ext i j
  show (if h : γ i = γ j ∧ ¬ δ j < δ i then (Pi.single t (1 : F) : LeviParIndex n γ δ → F)
    ⟨(i, j), h⟩ else 0) = _
  rw [Matrix.single_apply]
  by_cases hij : t.1.1 = i ∧ t.1.2 = j
  · obtain ⟨h1, h2⟩ := hij
    have ht : (⟨(i, j), h1 ▸ h2 ▸ t.2⟩ : LeviParIndex n γ δ) = t := by
      ext <;> simp [← h1, ← h2]
    rw [dif_pos (h1 ▸ h2 ▸ t.2), if_pos ⟨h1, h2⟩, ht, Pi.single_eq_same]
  · rw [if_neg hij]
    split_ifs with h
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hij ⟨rfl, rfl⟩
    · rfl

theorem mul_inv_apply_of_diagonal {g : GL (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) F) i i * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (1 : Matrix (Fin n) (Fin n) F) i j := by
  have h1 : ((g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) i j =
      (1 : Matrix (Fin n) (Fin n) F) i j := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hg i k (Ne.symm hk), zero_mul])
    (by simp)] at h1
  exact h1

theorem apply_self_ne_zero_of_diagonal {g : GL (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) F) i i ≠ 0 := by
  have h := mul_inv_apply_of_diagonal hg i i
  rw [one_apply_eq] at h
  exact left_ne_zero_of_mul_eq_one h

theorem inv_apply_of_diagonal {g : GL (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) (i j : Fin n) :
    ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      if i = j then ((g : Matrix (Fin n) (Fin n) F) i i)⁻¹ else 0 := by
  have h := mul_inv_apply_of_diagonal hg i j
  have h0 := apply_self_ne_zero_of_diagonal hg i
  have : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((g : Matrix (Fin n) (Fin n) F) i i)⁻¹ * (1 : Matrix (Fin n) (Fin n) F) i j := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  rw [this, one_apply]
  split_ifs <;> simp

theorem det_adLeviPar_of_diagonal (l : leviPar F n γ δ)
    (hl : ∀ i j, i ≠ j → ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :
    (LinearEquiv.det (adLeviPar F n γ δ l) : F) = ∏ s : LeviParIndex n γ δ,
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by
  classical
  have hQ : ∀ i j, i ≠ j →
      (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 :=
    fun i j hij => by rw [inv_apply_of_diagonal hl, if_neg hij]
  set P : Matrix (Fin n) (Fin n) F := ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Q : Matrix (Fin n) (Fin n) F :=
    (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let A : (LeviParIndex n γ δ → F) →ₗ[F] (LeviParIndex n γ δ → F) :=
    (((leviParCoord F n γ δ).symm.trans ((adLeviPar F n γ δ l).trans (leviParCoord F n γ δ))) :
      (LeviParIndex n γ δ → F) →ₗ[F] (LeviParIndex n γ δ → F))
  have hdet : (LinearEquiv.det (adLeviPar F n γ δ l) : F) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLeviPar F n γ δ l) (leviParCoord F n γ δ), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLeviPar F n γ δ l ((leviParCoord F n γ δ).symm (Pi.single t 1)) : lieLeviPar F n γ δ) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 = _
    rw [coe_adLeviPar, coe_leviParCoord_symm_single, mul_single_mul_apply]
  have hD : LinearMap.toMatrix' A = diagonal fun s : LeviParIndex n γ δ => P s.1.1 s.1.1 * Q s.1.2 s.1.2 := by
    ext s t
    rw [hM]
    by_cases hst : s = t
    · subst hst
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hst]
      by_cases h1 : s.1.1 = t.1.1
      · have h2 : t.1.2 ≠ s.1.2 := fun h2 => hst (Subtype.ext (Prod.ext h1 h2.symm))
        rw [hQ _ _ h2, mul_zero]
      · rw [hl _ _ h1, zero_mul]
  rw [hdet, ← LinearMap.det_toMatrix', hD, det_diagonal]

theorem modularCharacter_leviPar_of_diagonal (l : leviPar F n γ δ)
    (hl : ∀ i j, i ≠ j → ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :
    modularCharacter l = ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2},
      modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by
  classical
  rw [modularCharacter_leviPar, ← modulus_units, det_adLeviPar_of_diagonal l hl, map_prod]
  set f : Fin n → ℝ≥0 := fun i => modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i)
  have hf : ∀ i, f i ≠ 0 := fun i => modulus_ne_zero (apply_self_ne_zero_of_diagonal hl i)
  have hfac : ∀ s : LeviParIndex n γ δ,
      modulus (((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) =
      f s.1.1 / f s.1.2 := by
    intro s
    rw [map_mul, inv_apply_of_diagonal hl, if_pos rfl, map_inv₀, div_eq_mul_inv]
  rw [Finset.prod_congr rfl fun s _ => hfac s]
  change ∏ s : LeviParIndex n γ δ, f s.1.1 / f s.1.2 =
    ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2}, f s.1.1 / f s.1.2
  let g : Fin n × Fin n → ℝ≥0 := fun ij => f ij.1 / f ij.2
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n =>
        γ ij.1 = γ ij.2 ∧ ¬ δ ij.2 < δ ij.1) (by simp) g,
    ← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n =>
        γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2) (by simp) g]
  have hsplit : (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ ¬ δ ij.2 < δ ij.1) =
      (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2) ∪
        (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 = δ ij.2) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.le⟩
      · exact ⟨h1, h2.le⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2)
      (Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 = δ ij.2) := by
    rw [Finset.disjoint_filter]
    intro ij _ h1 h2
    exact h1.2.ne h2.2
  rw [hsplit, Finset.prod_union hdisj]
  set S := Finset.univ.filter fun ij : Fin n × Fin n => γ ij.1 = γ ij.2 ∧ δ ij.1 = δ ij.2
  have hswap : ∏ ij ∈ S, f ij.2 = ∏ ij ∈ S, f ij.1 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap (fun ij hij => ?_) (fun ij hij => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact ⟨hij.1.symm, hij.2.symm⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact ⟨hij.1.symm, hij.2.symm⟩
  have hone : ∏ ij ∈ S, g ij = 1 := by
    rw [Finset.prod_div_distrib, hswap, div_self]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hf _
  rw [hone, mul_one]

theorem diagPow_mem_leviPar (μ : Fin n → ℤ) : Cartan.diagPow F n μ ∈ leviPar F n γ δ := by
  refine ⟨diagPow_mem_levi μ, fun i j hij => ?_⟩
  have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
  show (Cartan.diagPow F n μ : Matrix (Fin n) (Fin n) F) i j = 0
  rw [Cartan.coe_diagPow, diagonal_apply_ne _ hne]

theorem modularCharacter_leviPar_diagPow (μ : Fin n → ℤ) :
    modularCharacter (⟨Cartan.diagPow F n μ, diagPow_mem_leviPar μ⟩ : leviPar F n γ δ) =
      ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2},
        modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) := by
  rw [modularCharacter_leviPar_of_diagonal _ fun i j hij => by
    show (Cartan.diagPow F n μ : Matrix (Fin n) (Fin n) F) i j = 0
    rw [Cartan.coe_diagPow, diagonal_apply_ne _ hij]]
  simp only [Cartan.coe_diagPow, diagonal_apply_eq]

end Diagonal

end Parabolic

end GroundTheory.Automorphic
