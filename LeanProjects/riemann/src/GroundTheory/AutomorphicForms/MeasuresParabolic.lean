import Mathlib
import GroundTheory.AutomorphicForms.MeasuresGL
import GroundTheory.AutomorphicForms.Iwasawa

namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)

def lieParabolic : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | A.BlockTriangular β}
  add_mem' ha hb := ha.add hb
  zero_mem' := Matrix.blockTriangular_zero
  smul_mem' c A hA i j hij := by
    simp [hA hij]

theorem mem_lieParabolic {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieParabolic F n β ↔ A.BlockTriangular β :=
  Iff.rfl

abbrev ParabolicIndex : Type := {ij : Fin n × Fin n // ¬ β ij.2 < β ij.1}

noncomputable def parabolicCoord : lieParabolic F n β ≃ₗ[F] (ParabolicIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : ¬ β j < β i then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β j < β i
    · simp [A.2 h]
    · simp [h]
  right_inv x := by
    funext s
    simp [s.2]

@[simp] theorem parabolicCoord_apply (A : lieParabolic F n β) (s : ParabolicIndex n β) :
    parabolicCoord F n β A s = (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

noncomputable def parabolicCoordHomeomorph : lieParabolic F n β ≃ₜ (ParabolicIndex n β → F) where
  toEquiv := (parabolicCoord F n β).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieParabolic F n β => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : β j < β i
    · simp only [Matrix.of_apply, h, not_true_eq_false, dite_false]
      exact continuous_const
    · simp only [Matrix.of_apply, h, not_false_eq_true, dite_true]
      exact continuous_apply _

def toLie (p : blockUpper F n β) : lieParabolic F n β :=
  ⟨((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), p.2⟩

theorem isClosed_blockUpper : IsClosed (blockUpper F n β : Set (GL (Fin n) F)) := by
  have : (blockUpper F n β : Set (GL (Fin n) F)) =
      ⋂ i, ⋂ j, ⋂ (_ : β j < β i), (fun g : GL (Fin n) F => g i j) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, mem_blockUpper, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (GLnLocal.continuous_entry F n i j)

instance locallyCompactSpace_blockUpper : LocallyCompactSpace (blockUpper F n β) :=
  (isClosed_blockUpper F n β).locallyCompactSpace

instance locallyCompactSpace_borel : LocallyCompactSpace (borel F n) :=
  locallyCompactSpace_blockUpper F n id

theorem isOpenEmbedding_toLie : IsOpenEmbedding (toLie F n β) := by
  have hemb : IsEmbedding (toLie F n β) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieParabolic F n β : Set (Matrix (Fin n) (Fin n) F)) fun p : blockUpper F n β => p.2
  refine ⟨hemb, ?_⟩
  have : Set.range (toLie F n β) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
      show (u : Matrix (Fin n) (Fin n) F).BlockTriangular β
      rw [hu]
      exact A.2
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val

noncomputable def mulLeftLie (p : blockUpper F n β) : lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (Units.mulLeftLinearEquiv F _ (p : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact p.2.mul hA
    · refine ⟨((p⁻¹ : blockUpper F n β) : GL (Fin n) F) * A, (p⁻¹).2.mul hA, ?_⟩
      simp [← mul_assoc])

noncomputable def mulRightLie (p : blockUpper F n β) :
    lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (Units.mulRightLinearEquiv F (p : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact hA.mul p.2
    · refine ⟨A * ((p⁻¹ : blockUpper F n β) : GL (Fin n) F), hA.mul (p⁻¹).2, ?_⟩
      simp [mul_assoc])

@[simp] theorem coe_mulLeftLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((mulLeftLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A :=
  rfl

@[simp] theorem coe_mulRightLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((mulRightLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      A * ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

noncomputable def adLie (p : blockUpper F n β) : lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (mulLeftLie F n β p).trans (mulRightLie F n β p⁻¹)

@[simp] theorem coe_adLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((adLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

noncomputable def parabolicChart : LinearChart F (ParabolicIndex n β) (blockUpper F n β) where
  toFun p := parabolicCoord F n β (toLie F n β p)
  isOpenEmbedding := by
    exact (parabolicCoordHomeomorph F n β).isOpenEmbedding.comp (isOpenEmbedding_toLie F n β)
  left p := (parabolicCoord F n β).symm.trans ((mulLeftLie F n β p).trans (parabolicCoord F n β))
  right p := (parabolicCoord F n β).symm.trans
    ((mulRightLie F n β p).trans (parabolicCoord F n β))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl

variable {F n β}

theorem parabolicChart_leftModulus (p : blockUpper F n β) :
    (parabolicChart F n β).leftModulus p =
      distribHaarChar F (LinearEquiv.det (mulLeftLie F n β p)) := by
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq]
  congr 1
  exact LinearEquiv.det_conj (mulLeftLie F n β p) (parabolicCoord F n β)

theorem parabolicChart_rightModulus (p : blockUpper F n β) :
    (parabolicChart F n β).rightModulus p =
      distribHaarChar F (LinearEquiv.det (mulRightLie F n β p)) := by
  rw [LinearChart.rightModulus, distribHaarChar_pi_eq]
  congr 1
  exact LinearEquiv.det_conj (mulRightLie F n β p) (parabolicCoord F n β)

theorem mulRightLie_inv (p : blockUpper F n β) :
    mulRightLie F n β p⁻¹ = (mulRightLie F n β p)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext A : 2
  show (A : Matrix (Fin n) (Fin n) F) * ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((p⁻¹ : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A
  simp [mul_assoc]

theorem modularCharacter_blockUpper (p : blockUpper F n β) :
    modularCharacter p = distribHaarChar F (LinearEquiv.det (adLie F n β p)) := by
  borelize F ↥(blockUpper F n β)
  rw [(parabolicChart F n β).modularCharacter_eq p, parabolicChart_leftModulus,
    parabolicChart_rightModulus]
  have : adLie F n β p = mulRightLie F n β p⁻¹ * mulLeftLie F n β p := rfl
  rw [this, mulRightLie_inv, map_mul, map_inv, map_mul, map_inv, div_eq_mul_inv, mul_comm]

section Triangular

theorem coe_parabolicCoord_symm_single (t : ParabolicIndex n β) :
    (((parabolicCoord F n β).symm (Pi.single t 1) : lieParabolic F n β) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by
  ext i j
  show (if h : ¬ β j < β i then (Pi.single t (1 : F) : ParabolicIndex n β → F) ⟨(i, j), h⟩
    else 0) = _
  rw [Matrix.single_apply]
  by_cases hij : t.1.1 = i ∧ t.1.2 = j
  · obtain ⟨h1, h2⟩ := hij
    have ht : (⟨(i, j), h1 ▸ h2 ▸ t.2⟩ : ParabolicIndex n β) = t := by
      ext <;> simp [← h1, ← h2]
    rw [dif_pos (h1 ▸ h2 ▸ t.2), if_pos ⟨h1, h2⟩, ht, Pi.single_eq_same]
  · rw [if_neg hij]
    split_ifs with h
    · rfl
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hij ⟨rfl, rfl⟩

theorem mul_single_mul_apply (A B : Matrix (Fin n) (Fin n) F) (a b i j : Fin n) :
    (A * Matrix.single a b (1 : F) * B) i j = A i a * B b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

theorem det_adLie_of_mem_borel (p : blockUpper F n β) (hp : (p : GL (Fin n) F) ∈ borel F n) :
    (LinearEquiv.det (adLie F n β p) : F) = ∏ s : ParabolicIndex n β,
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by
  classical
  set P : Matrix (Fin n) (Fin n) F := ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Q : Matrix (Fin n) (Fin n) F :=
    (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hP : P.IsUpperTriangular := hp
  have hQ : Q.IsUpperTriangular := (borel F n).inv_mem hp
  let A : (ParabolicIndex n β → F) →ₗ[F] (ParabolicIndex n β → F) :=
    (((parabolicCoord F n β).symm.trans ((adLie F n β p).trans (parabolicCoord F n β))) :
      (ParabolicIndex n β → F) →ₗ[F] (ParabolicIndex n β → F))
  have hdet : (LinearEquiv.det (adLie F n β p) : F) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLie F n β p) (parabolicCoord F n β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLie F n β p ((parabolicCoord F n β).symm (Pi.single t 1)) : lieParabolic F n β) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 = _
    rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]
  let κ : ParabolicIndex n β → Lex (Fin n × (Fin n)ᵒᵈ) :=
    fun s => toLex (s.1.1, OrderDual.toDual s.1.2)
  have hκ : Function.Injective κ := by
    intro s t h
    simp only [κ, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := by
    intro s t hts
    rw [hM]
    rcases Prod.Lex.lt_iff.1 hts with h | ⟨h1, h2⟩
    · have h' : t.1.1 < s.1.1 := h
      rw [hP h', zero_mul]
    · have h' : s.1.2 < t.1.2 := h2
      rw [hQ h', mul_zero]
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det, Finset.prod_image fun s _ t _ h => hκ h]
  refine Finset.prod_congr rfl fun s _ => ?_
  let : Unique {t // κ t = κ s} :=
    ⟨⟨⟨s, rfl⟩⟩, fun t => Subtype.ext (hκ t.2)⟩
  rw [Matrix.det_unique]
  show LinearMap.toMatrix' A (default : {t // κ t = κ s}).1 (default : {t // κ t = κ s}).1 = _
  rw [hM]
  rfl

theorem modularCharacter_blockUpper_of_mem_borel (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    modularCharacter p = ∏ s : ParabolicIndex n β,
      modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by
  rw [modularCharacter_blockUpper, ← modulus_units, det_adLie_of_mem_borel p hp, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul, inv_apply_self_of_mem_borel F n hp, map_inv₀, div_eq_mul_inv]

theorem modularCharacter_blockUpper_of_mem_borel' (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    modularCharacter p = ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
      modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by
  classical
  rw [modularCharacter_blockUpper_of_mem_borel p hp]
  set f : Fin n → ℝ≥0 := fun i => modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i)
  have hf : ∀ i, f i ≠ 0 := fun i => modulus_ne_zero (apply_self_ne_zero_of_mem_borel F n hp i)
  change ∏ s : ParabolicIndex n β, f s.1.1 / f s.1.2 =
    ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, f s.1.1 / f s.1.2
  let g : Fin n × Fin n → ℝ≥0 := fun ij => f ij.1 / f ij.2
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1)
      (by simp) g,
    ← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2)
      (by simp) g]
  have hsplit : (Finset.univ.filter fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1) =
      (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2) ∪
        (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_lt]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2)
      (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2) := by
    rw [Finset.disjoint_filter]
    intro ij _ h1 h2
    exact h1.ne h2
  rw [hsplit, Finset.prod_union hdisj]
  set S := Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2
  have hswap : ∏ ij ∈ S, f ij.2 = ∏ ij ∈ S, f ij.1 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap (fun ij hij => ?_) (fun ij hij => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact hij.symm
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact hij.symm
  have hone : ∏ ij ∈ S, g ij = 1 := by
    rw [Finset.prod_div_distrib, hswap, div_self]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hf _
  rw [hone, mul_one]

theorem modularCharacter_borel (b : blockUpper F n (id : Fin n → Fin n)) :
    modularCharacter b = ∏ i : Fin n,
      modulus (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i) ^ ((n : ℤ) - 1 - 2 * i) := by
  classical
  rw [modularCharacter_blockUpper_of_mem_borel b b.2]
  set f : Fin n → ℝ≥0 := fun i => modulus (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i)
  have hf : ∀ i, f i ≠ 0 := fun i => modulus_ne_zero (apply_self_ne_zero_of_mem_borel F n b.2 i)
  have hsub : ∀ g : Fin n × Fin n → ℝ≥0,
      ∏ s : ParabolicIndex n (id : Fin n → Fin n), g s.1 =
        ∏ i : Fin n, ∏ j : Fin n, if i ≤ j then g (i, j) else 1 := by
    intro g
    rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => ¬ ij.2 < ij.1)
      (by simp), Finset.prod_filter, Fintype.prod_prod_type]
    simp only [not_lt]
  change ∏ s : ParabolicIndex n (id : Fin n → Fin n), f s.1.1 / f s.1.2 = _
  rw [Finset.prod_div_distrib, hsub (fun ij => f ij.1), hsub (fun ij => f ij.2),
    Finset.prod_comm (f := fun i j => if i ≤ j then f j else 1)]
  have h1 : ∀ i : Fin n, (∏ j : Fin n, if i ≤ j then f i else 1) = f i ^ (n - i) := by
    intro i
    rw [← Finset.prod_filter, Finset.prod_const, Finset.filter_le_eq_Ici, Fin.card_Ici]
  have h2 : ∀ j : Fin n, (∏ i : Fin n, if i ≤ j then f j else 1) = f j ^ ((j : ℕ) + 1) := by
    intro j
    rw [← Finset.prod_filter, Finset.prod_const, Finset.filter_ge_eq_Iic, Fin.card_Iic]
  simp only [h1, h2]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hf i)]
  congr 1
  have := i.is_lt
  push_cast [Nat.cast_sub this.le]
  ring

theorem modularCharacter_borel' (b : borel F n) :
    modularCharacter b = ∏ i : Fin n,
      modulus (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i) ^ ((n : ℤ) - 1 - 2 * i) :=
  modularCharacter_borel b

end Triangular

section Unipotent

variable (F n β)

def lieUnipotent : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, ¬ β i < β j → A i j = 0}
  add_mem' {A B} ha hb i j h := by
    simp [ha i j h, hb i j h]
  zero_mem' _ _ _ := rfl
  smul_mem' c A hA i j h := by
    simp [hA i j h]

abbrev UnipotentIndex : Type := {ij : Fin n × Fin n // β ij.1 < β ij.2}

noncomputable def unipotentCoord : lieUnipotent F n β ≃ₗ[F] (UnipotentIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : β i < β j then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β i < β j
    · simp [h]
    · simp [h, A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]

variable {F n β}

theorem mul_mem_lieUnipotent {p X : Matrix (Fin n) (Fin n) F} (hp : p.BlockTriangular β)
    (hX : X ∈ lieUnipotent F n β) : p * X ∈ lieUnipotent F n β := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β k < β i
  · rw [hp hik, zero_mul]
  · rw [hX k j fun hkj => hij (lt_of_le_of_lt (not_lt.1 hik) hkj), mul_zero]

theorem mem_lieUnipotent_mul {p X : Matrix (Fin n) (Fin n) F} (hX : X ∈ lieUnipotent F n β)
    (hp : p.BlockTriangular β) : X * p ∈ lieUnipotent F n β := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β i < β k
  · rw [hp (lt_of_le_of_lt (not_lt.1 hij) hik), mul_zero]
  · rw [hX i k hik, zero_mul]

noncomputable def adUnipotent (p : blockUpper F n β) :
    lieUnipotent F n β ≃ₗ[F] lieUnipotent F n β :=
  ((Units.mulLeftLinearEquiv F _ (p : GL (Fin n) F)).trans
    (Units.mulRightLinearEquiv F ((p : GL (Fin n) F)⁻¹))).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mem_lieUnipotent_mul (mul_mem_lieUnipotent p.2 hA) (p⁻¹).2
    · refine ⟨((p⁻¹ : blockUpper F n β) : GL (Fin n) F) * A * (p : GL (Fin n) F),
        mem_lieUnipotent_mul (mul_mem_lieUnipotent (p⁻¹).2 hA) p.2, ?_⟩
      simp [mul_assoc])

@[simp] theorem coe_adUnipotent (p : blockUpper F n β) (A : lieUnipotent F n β) :
    ((adUnipotent p A : lieUnipotent F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

noncomputable def adUnipotentHom :
    blockUpper F n β →* (lieUnipotent F n β ≃ₗ[F] lieUnipotent F n β) where
  toFun := adUnipotent
  map_one' := LinearEquiv.ext fun A => Subtype.ext (by simp)
  map_mul' p q := LinearEquiv.ext fun A => Subtype.ext (by
    show ((adUnipotent (p * q) A : lieUnipotent F n β) : Matrix (Fin n) (Fin n) F) =
      ((adUnipotent p (adUnipotent q A) : lieUnipotent F n β) : Matrix (Fin n) (Fin n) F)
    simp [mul_assoc])

@[simp] theorem adUnipotentHom_apply (p : blockUpper F n β) :
    adUnipotentHom p = adUnipotent p :=
  rfl

theorem coe_unipotentCoord_symm_single (t : UnipotentIndex n β) :
    (((unipotentCoord F n β).symm (Pi.single t 1) : lieUnipotent F n β) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by
  ext i j
  show (if h : β i < β j then (Pi.single t (1 : F) : UnipotentIndex n β → F) ⟨(i, j), h⟩
    else 0) = _
  rw [Matrix.single_apply]
  by_cases hij : t.1.1 = i ∧ t.1.2 = j
  · obtain ⟨h1, h2⟩ := hij
    have hlt : β i < β j := h1 ▸ h2 ▸ t.2
    have ht : (⟨(i, j), hlt⟩ : UnipotentIndex n β) = t := by
      ext <;> simp [← h1, ← h2]
    rw [dif_pos hlt, if_pos ⟨h1, h2⟩, ht, Pi.single_eq_same]
  · rw [if_neg hij]
    split_ifs with h
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hij ⟨rfl, rfl⟩
    · rfl

theorem det_adUnipotent_of_mem_borel (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    (LinearEquiv.det (adUnipotent p) : F) = ∏ s : UnipotentIndex n β,
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by
  classical
  set P : Matrix (Fin n) (Fin n) F := ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Q : Matrix (Fin n) (Fin n) F :=
    (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hP : P.IsUpperTriangular := hp
  have hQ : Q.IsUpperTriangular := (borel F n).inv_mem hp
  let A : (UnipotentIndex n β → F) →ₗ[F] (UnipotentIndex n β → F) :=
    (((unipotentCoord F n β).symm.trans ((adUnipotent p).trans (unipotentCoord F n β))) :
      (UnipotentIndex n β → F) →ₗ[F] (UnipotentIndex n β → F))
  have hdet : (LinearEquiv.det (adUnipotent p) : F) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adUnipotent p) (unipotentCoord F n β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adUnipotent p ((unipotentCoord F n β).symm (Pi.single t 1)) : lieUnipotent F n β) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 = _
    rw [coe_adUnipotent, coe_unipotentCoord_symm_single, mul_single_mul_apply]
  let κ : UnipotentIndex n β → Lex (Fin n × (Fin n)ᵒᵈ) :=
    fun s => toLex (s.1.1, OrderDual.toDual s.1.2)
  have hκ : Function.Injective κ := by
    intro s t h
    simp only [κ, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := by
    intro s t hts
    rw [hM]
    rcases Prod.Lex.lt_iff.1 hts with h | ⟨h1, h2⟩
    · have h' : t.1.1 < s.1.1 := h
      rw [hP h', zero_mul]
    · have h' : s.1.2 < t.1.2 := h2
      rw [hQ h', mul_zero]
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det, Finset.prod_image fun s _ t _ h => hκ h]
  refine Finset.prod_congr rfl fun s _ => ?_
  let : Unique {t // κ t = κ s} :=
    ⟨⟨⟨s, rfl⟩⟩, fun t => Subtype.ext (hκ t.2)⟩
  rw [Matrix.det_unique]
  show LinearMap.toMatrix' A (default : {t // κ t = κ s}).1 (default : {t // κ t = κ s}).1 = _
  rw [hM]
  rfl

theorem mul_mul_apply_mem_integer {A M B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hM : ∀ i j, M i j ∈ 𝒪[F]) (hB : ∀ i j, B i j ∈ 𝒪[F]) (i j : Fin n) :
    (A * M * B) i j ∈ 𝒪[F] := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ (hB b j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hA i a) (hM a b)

theorem adUnipotent_symm (p : blockUpper F n β) : (adUnipotent p).symm = adUnipotent p⁻¹ := by
  refine LinearEquiv.ext fun A => ?_
  rw [LinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  simp [mul_assoc]

theorem distribHaarChar_det_adUnipotent_of_mem_integralGL (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ GLnLocal.integralGL F n) :
    distribHaarChar F (LinearEquiv.det (adUnipotent p)) = 1 := by
  obtain ⟨h₁, h₂⟩ := (GLnLocal.mem_integralGL_iff F n).1 hp
  have hint : ∀ (q : blockUpper F n β),
      (∀ i j, ((q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) →
      (∀ i j, (((q : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) →
      ∀ x ∈ box F (UnipotentIndex n β),
        unipotentCoord F n β (adUnipotent q ((unipotentCoord F n β).symm x)) ∈
          box F (UnipotentIndex n β) := by
    intro q hq hq' x hx
    refine mem_box.2 fun s => ?_
    show ((adUnipotent q ((unipotentCoord F n β).symm x) : lieUnipotent F n β) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 ∈ 𝒪[F]
    rw [coe_adUnipotent]
    refine mul_mul_apply_mem_integer hq (fun i j => ?_) hq' _ _
    show (if h : β i < β j then x ⟨(i, j), h⟩ else 0) ∈ 𝒪[F]
    split_ifs
    · exact mem_box.1 hx _
    · exact Subring.zero_mem _
  rw [← LinearEquiv.det_conj (adUnipotent p) (unipotentCoord F n β), ← distribHaarChar_pi_eq]
  refine distribHaarChar_eq_one_of_mapsTo_box (fun x hx => hint p h₁ h₂ x hx) fun x hx => ?_
  show unipotentCoord F n β ((adUnipotent p).symm ((unipotentCoord F n β).symm x)) ∈ _
  rw [adUnipotent_symm]
  refine hint p⁻¹ (fun i j => ?_) (fun i j => ?_) x hx
  · simpa using h₂ i j
  · simpa using h₁ i j

theorem modularCharacter_eq_one_of_mem_integralGL (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ GLnLocal.integralGL F n) : modularCharacter p = 1 := by
  borelize F ↥(blockUpper F n β)
  let V : OpenSubgroup (blockUpper F n β) :=
    ⟨(GLnLocal.integralGL F n).subgroupOf (blockUpper F n β),
      (GLnLocal.isOpen_integralGL F n).preimage continuous_subtype_val⟩
  have hV : IsCompact (V : Set (blockUpper F n β)) :=
    (isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GLnLocal.isCompact_integralGL F n)
  obtain ⟨h1, h2⟩ := (parabolicChart F n β).modulus_eq_one_of_mem hV (v := p) hp
  rw [(parabolicChart F n β).modularCharacter_eq, h1, h2, div_one]

theorem modularCharacter_blockUpper_eq_det_adUnipotent (hβ : Monotone β) (p : blockUpper F n β) :
    modularCharacter p = distribHaarChar F (LinearEquiv.det (adUnipotent p)) := by
  obtain ⟨b, hb, k, hk, hbk⟩ := exists_borel_mul_integralGL F n (p : GL (Fin n) F)
  let b' : blockUpper F n β := ⟨b, borel_le_blockUpper F n hβ hb⟩
  have hkP : k ∈ blockUpper F n β := by
    have : k = b⁻¹ * (p : GL (Fin n) F) := by
      rw [hbk]
      group
    rw [this]
    exact mul_mem (inv_mem b'.2) p.2
  let k' : blockUpper F n β := ⟨k, hkP⟩
  have hp : p = b' * k' := Subtype.ext hbk
  have hχ : distribHaarChar F (LinearEquiv.det (adUnipotent p)) =
      distribHaarChar F (LinearEquiv.det (adUnipotent b')) *
        distribHaarChar F (LinearEquiv.det (adUnipotent k')) := by
    rw [← adUnipotentHom_apply, hp, map_mul, map_mul, map_mul]
    rfl
  rw [hχ, hp, map_mul, modularCharacter_eq_one_of_mem_integralGL k' hk,
    distribHaarChar_det_adUnipotent_of_mem_integralGL k' hk, mul_one, mul_one,
    modularCharacter_blockUpper_of_mem_borel' b' hb, ← modulus_units,
    det_adUnipotent_of_mem_borel b' hb, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul, inv_apply_self_of_mem_borel F n hb, map_inv₀, div_eq_mul_inv]

end Unipotent

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

noncomputable def haarParabolic (μ₀ : Measure (ParabolicIndex n β → F)) :
    Measure (blockUpper F n β) :=
  (parabolicChart F n β).haar μ₀

variable (μ₀ : Measure (ParabolicIndex n β → F)) [μ₀.IsAddHaarMeasure]

instance isHaarMeasure_haarParabolic : (haarParabolic μ₀).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ₀

theorem haarParabolic_eq :
    haarParabolic μ₀ = (μ₀.comap fun (p : blockUpper F n β) (s : ParabolicIndex n β) =>
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2).withDensity
        fun p => (((distribHaarChar F (LinearEquiv.det (mulLeftLie F n β p)))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [haarParabolic, LinearChart.haar]
  congr 1
  funext p
  rw [parabolicChart_leftModulus]

theorem map_mul_right_haarParabolic (p : blockUpper F n β) :
    map (· * p) (haarParabolic μ₀) =
      distribHaarChar F (LinearEquiv.det (adLie F n β p)) • haarParabolic μ₀ := by
  rw [haarParabolic, (parabolicChart F n β).map_mul_right_haar, ←
    (parabolicChart F n β).modularCharacter_eq, modularCharacter_blockUpper]

end Measures

end GroundTheory.Automorphic
