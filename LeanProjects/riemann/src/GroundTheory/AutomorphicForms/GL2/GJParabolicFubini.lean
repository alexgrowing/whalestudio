import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.Measures
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]

variable (n) in

abbrev LeviIndex (β : Fin n → α) : Type := {ij : Fin n × Fin n // β ij.1 = β ij.2}

variable (F) in

def unipMatrix {β : Fin n → α} (u : UnipotentIndex n β → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if h : β i < β j then u ⟨(i, j), h⟩ else 0

theorem unipMatrix_apply_of_lt {β : Fin n → α} (u : UnipotentIndex n β → F) {i j : Fin n}
    (h : β i < β j) : unipMatrix F u i j = u ⟨(i, j), h⟩ := by
  simp [unipMatrix, h]

theorem unipMatrix_apply_of_not_lt {β : Fin n → α} (u : UnipotentIndex n β → F) {i j : Fin n}
    (h : ¬ β i < β j) : unipMatrix F u i j = 0 := by
  simp [unipMatrix, h]

section Chart

variable (F n) (β : Fin n → α)

def lieLevi : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, β i ≠ β j → A i j = 0}
  add_mem' {A B} hA hB i j h := by simp [hA i j h, hB i j h]
  zero_mem' i j _ := rfl
  smul_mem' c A hA i j h := by simp [hA i j h]

variable {F n β} in
theorem mem_lieLevi {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLevi F n β ↔ ∀ i j, β i ≠ β j → A i j = 0 :=
  Iff.rfl

variable {F n β} in

theorem mul_mem_lieLevi {A B : Matrix (Fin n) (Fin n) F} (hA : A ∈ lieLevi F n β)
    (hB : B ∈ lieLevi F n β) : A * B ∈ lieLevi F n β := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β i = β k
  · rw [hB k j (fun e => h (hik.trans e)), mul_zero]
  · rw [hA i k hik, zero_mul]

def leviCoord : lieLevi F n β ≃ₗ[F] (LeviIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : β i = β j then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β i = β j
    · simp [h]
    · simp [h, A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]

@[simp] theorem leviCoord_apply (A : lieLevi F n β) (s : LeviIndex n β) :
    leviCoord F n β A s = (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

def leviCoordHomeomorph : lieLevi F n β ≃ₜ (LeviIndex n β → F) where
  toEquiv := (leviCoord F n β).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieLevi F n β => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : β i = β j
    · simp only [Matrix.of_apply, h, dite_true]
      exact continuous_apply _
    · simp only [Matrix.of_apply, h, dite_false]
      exact continuous_const

def toLieLevi (m : levi F n β) : lieLevi F n β :=
  ⟨((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), fun i j h => mem_levi.1 m.2 i j h⟩

theorem isOpenEmbedding_toLieLevi : IsOpenEmbedding (toLieLevi F n β) := by
  have hemb : IsEmbedding (toLieLevi F n β) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieLevi F n β : Set (Matrix (Fin n) (Fin n) F)) fun m : levi F n β =>
        fun i j h => mem_levi.1 m.2 i j h
  refine ⟨hemb, ?_⟩
  have : Set.range (toLieLevi F n β) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, mem_levi.2 fun i j h => ?_⟩, Subtype.ext hu⟩
      rw [hu]
      exact A.2 i j h
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val

def mulLeftLieLevi (m : levi F n β) : lieLevi F n β ≃ₗ[F] lieLevi F n β :=
  (Units.mulLeftLinearEquiv F _ (m : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLevi (fun i j h => mem_levi.1 m.2 i j h) hA
    · refine ⟨((m⁻¹ : levi F n β) : GL (Fin n) F) * A,
        mul_mem_lieLevi (fun i j h => mem_levi.1 (m⁻¹).2 i j h) hA, ?_⟩
      simp [← mul_assoc])

def mulRightLieLevi (m : levi F n β) : lieLevi F n β ≃ₗ[F] lieLevi F n β :=
  (Units.mulRightLinearEquiv F (m : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLevi hA (fun i j h => mem_levi.1 m.2 i j h)
    · refine ⟨A * ((m⁻¹ : levi F n β) : GL (Fin n) F),
        mul_mem_lieLevi hA (fun i j h => mem_levi.1 (m⁻¹).2 i j h), ?_⟩
      simp [mul_assoc])

variable {F n}

def leviChart : LinearChart F (LeviIndex n β) (levi F n β) where
  toFun m := leviCoord F n β (toLieLevi F n β m)
  isOpenEmbedding :=
    (leviCoordHomeomorph F n β).isOpenEmbedding.comp (isOpenEmbedding_toLieLevi F n β)
  left m := (leviCoord F n β).symm.trans ((mulLeftLieLevi F n β m).trans (leviCoord F n β))
  right m := (leviCoord F n β).symm.trans ((mulRightLieLevi F n β m).trans (leviCoord F n β))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl

variable {β}

@[simp] theorem leviChart_apply (m : levi F n β) (s : LeviIndex n β) :
    (leviChart β).toFun m s = ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

@[simp] theorem parabolicChart_apply (p : blockUpper F n β) (s : ParabolicIndex n β) :
    (parabolicChart F n β).toFun p s = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl

end Chart

section ParabolicMk

variable {β : Fin n → α}

theorem blockTriangular_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u).BlockTriangular β := by
  intro i j hji
  rw [Matrix.add_apply, mem_levi.1 m.2 i j (ne_of_gt hji),
    unipMatrix_apply_of_not_lt u (not_lt.2 hji.le), add_zero]

theorem det_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u).det =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
  classical
  have hm : ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular β :=
    fun i j h => mem_levi.1 m.2 i j (ne_of_gt h)
  rw [(blockTriangular_add_unipMatrix m u).det, hm.det]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply]
  rw [unipMatrix_apply_of_not_lt u (by rw [i.2, j.2]; exact lt_irrefl _), add_zero]

theorem isUnit_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    IsUnit (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_add_unipMatrix, ← Matrix.isUnit_iff_isUnit_det]
  exact (m : GL (Fin n) F).isUnit

variable (β) in

def parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) : blockUpper F n β :=
  ⟨(isUnit_add_unipMatrix m u).unit, by
    rw [mem_blockUpper, IsUnit.unit_spec]
    exact blockTriangular_add_unipMatrix m u⟩

theorem coe_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u :=
  IsUnit.unit_spec _

theorem leviProj_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    leviProj F n β (parabolicMk β m u) = m := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [leviProj_apply, coe_parabolicMk]
  split_ifs with h
  · rw [Matrix.add_apply, unipMatrix_apply_of_not_lt u (by rw [h]; exact lt_irrefl _), add_zero]
  · exact (mem_levi.1 m.2 i j h).symm

def unipCoord (p : blockUpper F n β) : UnipotentIndex n β → F :=
  fun s => ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2

theorem unipCoord_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    unipCoord (parabolicMk β m u) = u := by
  funext s
  rw [unipCoord, coe_parabolicMk, Matrix.add_apply, mem_levi.1 m.2 _ _ (ne_of_lt s.2),
    unipMatrix_apply_of_lt u s.2, zero_add]

theorem parabolicMk_leviProj_unipCoord (p : blockUpper F n β) :
    parabolicMk β (leviProj F n β p) (unipCoord p) = p := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [coe_parabolicMk, Matrix.add_apply, leviProj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · rw [if_neg (ne_of_lt h), unipMatrix_apply_of_lt _ h, zero_add]
    rfl
  · rw [if_pos h, unipMatrix_apply_of_not_lt _ (by rw [h]; exact lt_irrefl _), add_zero]
  · rw [if_neg (ne_of_gt h), unipMatrix_apply_of_not_lt _ (not_lt.2 h.le), add_zero]
    exact ((mem_blockUpper F n).1 p.2 h).symm

end ParabolicMk

section Ratio

instance locallyCompactSpace_levi_chart (β : Fin n → α) : LocallyCompactSpace (levi F n β) :=
  isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace

variable (β : Fin n → α)

def leviRatio : levi F n β →* ℝ≥0 where
  toFun m := (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m)
  map_one' := by
    borelize F ↥(levi F n β) ↥(blockUpper F n β)
    rw [map_one, ← LinearChart.leftModulusHom_apply, ← LinearChart.leftModulusHom_apply, map_one,
      map_one, div_one]
  map_mul' m m' := by
    borelize F ↥(levi F n β) ↥(blockUpper F n β)
    rw [map_mul, LinearChart.leftModulus_mul, LinearChart.leftModulus_mul, div_mul_div_comm]

theorem leviRatio_apply (m : levi F n β) :
    leviRatio β m = (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m) :=
  rfl

variable {β}

theorem continuous_leviRatio : Continuous (leviRatio (F := F) β) := by
  borelize F ↥(levi F n β) ↥(blockUpper F n β)
  show Continuous fun m : levi F n β =>
    (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m)
  refine Continuous.div (LinearChart.continuous_leftModulus _) ?_ fun m =>
    (LinearChart.leftModulus_pos _ _).ne'
  exact (LinearChart.continuous_leftModulus _).comp
    (continuous_subtype_val.subtype_mk _ : Continuous fun m : levi F n β => leviIncl m)

end Ratio

section Coordinates

variable (β : Fin n → α)

def coordAddEquiv : ((LeviIndex n β → F) × (UnipotentIndex n β → F)) ≃+ (ParabolicIndex n β → F) where
  toFun x s := if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩
    else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩
  invFun y := (fun s => y ⟨s.1, not_lt.2 s.2.le⟩, fun s => y ⟨s.1, not_lt.2 s.2.le⟩)
  left_inv x := by
    ext s
    · simp [s.2]
    · simp [ne_of_lt s.2]
  right_inv y := by
    funext s
    by_cases h : β s.1.1 = β s.1.2 <;> simp [h]
  map_add' x y := by
    funext s
    by_cases h : β s.1.1 = β s.1.2 <;> simp [h]

theorem coordAddEquiv_apply (x : (LeviIndex n β → F) × (UnipotentIndex n β → F))
    (s : ParabolicIndex n β) :
    coordAddEquiv β x s = if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩
      else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩ :=
  rfl

def coordEquiv : ((LeviIndex n β → F) × (UnipotentIndex n β → F)) ≃ₜ+ (ParabolicIndex n β → F) where
  toAddEquiv := coordAddEquiv β
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    show Continuous fun x : (LeviIndex n β → F) × (UnipotentIndex n β → F) =>
      if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩ else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩
    by_cases h : β s.1.1 = β s.1.2
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_fst
    · simp only [h, dite_false]
      exact (continuous_apply _).comp continuous_snd
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun s => ?_) (continuous_pi fun s => ?_) <;>
    exact continuous_apply _

theorem coe_coordEquiv : ⇑(coordEquiv (F := F) β) = coordAddEquiv β := rfl

variable {β}

theorem continuous_leviProj : Continuous (leviProj F n β) := by
  refine (leviChart β).isOpenEmbedding.isInducing.continuous_iff.2 ?_
  have : (leviChart β).toFun ∘ leviProj F n β = fun (p : blockUpper F n β) (s : LeviIndex n β) =>
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 := by
    funext p s
    simp only [Function.comp_apply, leviChart_apply, leviProj_apply, if_pos s.2]
  rw [this]
  exact continuous_pi fun s =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem s.1.1 s.1.2

theorem parabolicChart_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (parabolicChart F n β).toFun (parabolicMk β m u) = coordAddEquiv β ((leviChart β).toFun m, u) := by
  funext s
  rw [parabolicChart_apply, coe_parabolicMk, Matrix.add_apply, coordAddEquiv_apply]
  by_cases h : β s.1.1 = β s.1.2
  · rw [dif_pos h, unipMatrix_apply_of_not_lt u (by rw [h]; exact lt_irrefl _), add_zero]
    rfl
  · have hlt := lt_of_le_of_ne (not_lt.1 s.2) h
    rw [dif_neg h, mem_levi.1 m.2 _ _ h, unipMatrix_apply_of_lt u hlt, zero_add]

variable (β) in

def parabolicMkHomeomorph : (levi F n β × (UnipotentIndex n β → F)) ≃ₜ blockUpper F n β where
  toFun x := parabolicMk β x.1 x.2
  invFun p := (leviProj F n β p, unipCoord p)
  left_inv x := Prod.ext (leviProj_parabolicMk x.1 x.2) (unipCoord_parabolicMk x.1 x.2)
  right_inv p := parabolicMk_leviProj_unipCoord p
  continuous_toFun := by
    refine (parabolicChart F n β).isOpenEmbedding.isInducing.continuous_iff.2 ?_
    have : (parabolicChart F n β).toFun ∘ (fun x : levi F n β × (UnipotentIndex n β → F) =>
        parabolicMk β x.1 x.2) = fun x => coordEquiv β ((leviChart β).toFun x.1, x.2) := by
      funext x
      rw [Function.comp_apply, parabolicChart_parabolicMk]
      rfl
    rw [this]
    exact (coordEquiv β).continuous.comp
      (((leviChart β).isOpenEmbedding.continuous.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := by
    refine continuous_leviProj.prodMk (continuous_pi fun s => ?_)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem s.1.1 s.1.2

end Coordinates

theorem eq_one_of_mem_compact {G : Type*} [Group G] [TopologicalSpace G] (χ : G →* ℝ≥0)
    (hχ : Continuous χ) {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) :
    χ k = 1 := by
  obtain ⟨B, hB⟩ := (hK.image hχ).bddAbove
  have hbd : ∀ x ∈ K, χ x ≤ B := fun x hx => hB ⟨x, hx, rfl⟩
  have key : ∀ x ∈ K, ¬ 1 < χ x := fun x hx h1 => by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B h1
    rw [← map_pow] at hN
    exact (hbd _ (K.pow_mem hx N)).not_gt hN
  have hne : χ k ≠ 0 := by
    intro h0
    have := map_mul_eq_one χ (mul_inv_cancel k)
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  rcases lt_trichotomy (χ k) 1 with h | h | h
  · exfalso
    refine key k⁻¹ (K.inv_mem hk) ?_
    rw [map_inv]
    exact one_lt_inv₀ (pos_iff_ne_zero.2 hne) |>.2 h
  · exact h
  · exact absurd h (key k hk)

section Measures

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

variable {β : Fin n → α}

variable (β) in

def haarLevi (μ𝔪 : Measure (LeviIndex n β → F)) : Measure (levi F n β) :=
  (leviChart β).haar μ𝔪

instance isHaarMeasure_haarLevi (μ𝔪 : Measure (LeviIndex n β → F)) [μ𝔪.IsAddHaarMeasure] :
    (haarLevi β μ𝔪).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ𝔪

variable (β) in

def parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F)) (μ𝔫 : Measure (UnipotentIndex n β → F)) :
    Measure (ParabolicIndex n β → F) :=
  map (coordEquiv β) (μ𝔪.prod μ𝔫)

instance isAddHaarMeasure_parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).IsAddHaarMeasure :=
  ContinuousAddEquiv.isAddHaarMeasure_map _ _

theorem parabolicChart_leftModulus_of_mem {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ unipotentRadical F n β) :
    (parabolicChart F n β).leftModulus p = 1 := by
  obtain ⟨K, hKc, -, hK⟩ := exists_compactOpen_unipotentRadical
    ({⟨(p : GL (Fin n) F), hp⟩} : Finset (unipotentRadical F n β))
  have hle : ∀ x : unipotentRadical F n β, (x : GL (Fin n) F) ∈ blockUpper F n β :=
    fun x => (mem_unipotentRadical.1 x.2).1
  let φ : unipotentRadical F n β →* blockUpper F n β :=
    { toFun := fun x => ⟨x, hle x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Continuous φ := continuous_induced_rng.2 continuous_subtype_val
  have := eq_one_of_mem_compact (((parabolicChart F n β).leftModulusHom).comp φ)
    ((LinearChart.continuous_leftModulus _).comp hφ) hKc (hK _ (Finset.mem_singleton_self _))
  exact this

theorem parabolicChart_leftModulus_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (parabolicChart F n β).leftModulus (parabolicMk β m u) =
      (parabolicChart F n β).leftModulus (leviIncl m) := by
  have h := leviProj_inv_mul_mem (parabolicMk β m u)
  rw [leviProj_parabolicMk] at h
  have e : parabolicMk β m u = leviIncl m * ((leviIncl m)⁻¹ * parabolicMk β m u) := by group
  rw [e, LinearChart.leftModulus_mul, parabolicChart_leftModulus_of_mem h, mul_one]

theorem comap_parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).comap (parabolicChart F n β).toFun =
      map (parabolicMkHomeomorph β) ((μ𝔪.comap (leviChart β).toFun).prod μ𝔫) := by
  ext S hS
  have hSP := (parabolicChart F n β).measurableEmbedding.measurableSet_image.2 hS
  have hΘ : Measurable (parabolicMkHomeomorph (F := F) β) :=
    (parabolicMkHomeomorph β).continuous.measurable
  have hE : Measurable (coordEquiv (F := F) β) := (coordEquiv β).continuous.measurable
  rw [(parabolicChart F n β).measurableEmbedding.comap_apply, parabolicMeasure,
    map_apply hE hSP, map_apply hΘ hS, Measure.prod_apply (hE hSP), Measure.prod_apply (hΘ hS)]
  set G : (LeviIndex n β → F) → ℝ≥0∞ := fun a =>
    μ𝔫 (Prod.mk a ⁻¹' (coordEquiv β ⁻¹' ((parabolicChart F n β).toFun '' S))) with hG
  have hslice : ∀ m : levi F n β,
      μ𝔫 (Prod.mk m ⁻¹' (parabolicMkHomeomorph β ⁻¹' S)) = G ((leviChart β).toFun m) := by
    intro m
    rw [hG]
    congr 1
    ext u
    simp only [Set.mem_preimage]
    show parabolicMk β m u ∈ S ↔ coordEquiv β ((leviChart β).toFun m, u) ∈ _
    rw [coe_coordEquiv, ← parabolicChart_parabolicMk,
      (parabolicChart F n β).isOpenEmbedding.injective.mem_set_image]
  have hsupp : Function.support G ⊆ Set.range (leviChart β).toFun := by
    intro a ha
    obtain ⟨u, p, -, hp⟩ : ∃ u, coordEquiv β (a, u) ∈ (parabolicChart F n β).toFun '' S := by
      by_contra h
      push Not at h
      apply ha
      rw [hG]
      convert measure_empty (μ := μ𝔫)
      ext u
      simpa using h u
    refine ⟨leviProj F n β p, ?_⟩
    have e := congrArg (fun y => ((coordAddEquiv β).symm y).1) hp
    simp only [coe_coordEquiv, AddEquiv.symm_apply_apply] at e
    rw [← e]
    funext s
    rw [leviChart_apply, leviProj_apply, if_pos s.2]
    rfl
  rw [show (fun x : levi F n β => μ𝔫 (Prod.mk x ⁻¹' (parabolicMkHomeomorph β ⁻¹' S))) =
      fun m => G ((leviChart β).toFun m) from funext hslice,
    ← (leviChart β).measurableEmbedding.lintegral_map, (leviChart β).measurableEmbedding.map_comap,
    setLIntegral_eq_of_support_subset hsupp]

end Measures

section Main

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

variable {β : Fin n → α}

theorem withDensity_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
    (ν : Measure X) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (map e ν).withDensity f = map e (ν.withDensity (f ∘ e)) := by
  ext S hS
  rw [withDensity_apply _ hS, map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    setLIntegral_map hS hf e.measurable]
  rfl

theorem haarParabolic_eq_map (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    haarParabolic (parabolicMeasure β μ𝔪 μ𝔫) =
      map (parabolicMkHomeomorph β)
        (((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)).prod μ𝔫) := by
  have hθ : Measurable fun m : levi F n β => (leviRatio β m : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp continuous_leviRatio).measurable
  have hρM := (leviChart (F := F) β).measurable_density
  show ((parabolicMeasure β μ𝔪 μ𝔫).comap (parabolicChart F n β).toFun).withDensity _ = _
  rw [comap_parabolicMeasure, ← Homeomorph.toMeasurableEquiv_coe,
    withDensity_map_equiv _ _ (parabolicChart F n β).measurable_density]
  congr 1
  have hfun : ((fun p : blockUpper F n β =>
      ((((parabolicChart F n β).leftModulus p)⁻¹ : ℝ≥0) : ℝ≥0∞)) ∘
        (parabolicMkHomeomorph β).toMeasurableEquiv) =
      fun z => (fun m : levi F n β => ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        (leviRatio β m : ℝ≥0∞)) z.1 * (1 : (UnipotentIndex n β → F) → ℝ≥0∞) z.2 := by
    funext z
    simp only [Function.comp_apply, Homeomorph.toMeasurableEquiv_coe, Pi.one_apply, mul_one]
    show ((((parabolicChart F n β).leftModulus (parabolicMk β z.1 z.2))⁻¹ : ℝ≥0) : ℝ≥0∞) = _
    rw [parabolicChart_leftModulus_parabolicMk, leviRatio_apply, ← ENNReal.coe_mul]
    congr 1
    have h1 := ((leviChart β).leftModulus_pos z.1).ne'
    have h2 := ((parabolicChart F n β).leftModulus_pos (leviIncl z.1)).ne'
    field_simp
  rw [hfun, ← prod_withDensity (f := fun m : levi F n β =>
      ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞) * (leviRatio β m : ℝ≥0∞))
      (hρM.mul hθ) measurable_one, withDensity_one]
  rw [show (fun m : levi F n β =>
      ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞) * (leviRatio β m : ℝ≥0∞)) =
      (fun m : levi F n β => ((((leviChart β).leftModulus m)⁻¹ : ℝ≥0) : ℝ≥0∞)) *
        (fun m : levi F n β => (leviRatio β m : ℝ≥0∞)) from rfl, withDensity_mul _ hρM hθ]
  rfl

theorem lintegral_haarParabolic (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    {H : blockUpper F n β → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H p ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫⁻ m, (leviRatio β m : ℝ≥0∞) * ∫⁻ u, H (parabolicMk β m u) ∂μ𝔫 ∂(haarLevi β μ𝔪) := by
  have hθ : Measurable fun m : levi F n β => (leviRatio β m : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp continuous_leviRatio).measurable
  have hHΘ : Measurable fun z : levi F n β × (UnipotentIndex n β → F) =>
      H (parabolicMkHomeomorph β z) := hH.comp (parabolicMkHomeomorph β).continuous.measurable
  rw [haarParabolic_eq_map, (parabolicMkHomeomorph β).measurableEmbedding.lintegral_map,
    lintegral_prod _ hHΘ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hθ hHΘ.lintegral_prod_right']
  rfl

theorem integral_haarParabolic (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure]
    {H : blockUpper F n β → ℂ} (hH : Integrable H (haarParabolic (parabolicMeasure β μ𝔪 μ𝔫))) :
    ∫ p, H p ∂(haarParabolic (parabolicMeasure β μ𝔪 μ𝔫)) =
      ∫ m, (leviRatio β m : ℂ) * ∫ u, H (parabolicMk β m u) ∂μ𝔫 ∂(haarLevi β μ𝔪) := by
  have hθ : Measurable fun m : levi F n β => leviRatio β m :=
    continuous_leviRatio.measurable
  rw [haarParabolic_eq_map] at hH ⊢
  have hΘ := (parabolicMkHomeomorph (F := F) β).measurableEmbedding
  rw [hΘ.integral_map]
  calc ∫ z, H (parabolicMkHomeomorph β z)
        ∂((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)).prod μ𝔫
      = ∫ m, ∫ u, H (parabolicMkHomeomorph β (m, u)) ∂μ𝔫
          ∂((haarLevi β μ𝔪).withDensity fun m => (leviRatio β m : ℝ≥0∞)) :=
        integral_prod _ ((hΘ.integrable_map_iff).1 hH)
    _ = ∫ m, leviRatio β m • ∫ u, H (parabolicMkHomeomorph β (m, u)) ∂μ𝔫 ∂(haarLevi β μ𝔪) :=
        integral_withDensity_eq_integral_smul hθ _
    _ = _ := by
        congr 1

theorem isLeviSchwartz_integral (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔫.IsAddHaarMeasure]
    {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    IsLeviSchwartz β (fun X => ∫ u, Φ (X + unipMatrix F u) ∂μ𝔫) := by
  obtain ⟨r, A, hinv, hsupp⟩ := hΦ.exists_invariant
  refine ⟨r, A, fun X Y _ _ hY => ?_, fun X hX hne i j => ?_⟩
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [add_right_comm]
    exact hinv _ Y hY
  · by_cases hij : β i = β j
    · by_contra h
      apply hne
      have hz : (fun u : UnipotentIndex n β → F => Φ (X + unipMatrix F u)) = 0 := by
        funext u
        by_contra h'
        apply h
        have := hsupp _ h' i j
        rwa [Matrix.add_apply, unipMatrix_apply_of_not_lt u (by rw [hij]; exact lt_irrefl _),
          add_zero] at this
      simp only
      rw [hz]
      exact integral_zero _ _
    · rw [hX i j hij, mul_zero]
      exact zero_mem _

end Main

end GodementJacquet

end GroundTheory.Automorphic
