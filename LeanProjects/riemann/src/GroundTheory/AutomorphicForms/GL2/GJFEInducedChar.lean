import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEInducedInv

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Measures MeasureTheory
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] in

theorem det_eq_prod_of_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → F) ≃ₗ[F] (ι → F)) (c : ι → F) (h : ∀ x s, L x s = c s * x s) :
    (LinearEquiv.det L : F) = ∏ s, c s := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  have : LinearMap.toMatrix' (L : (ι → F) →ₗ[F] (ι → F)) = Matrix.diagonal c := by
    ext s t
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, h, Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [this, Matrix.det_diagonal]

omit [MeasurableSpace F] [BorelSpace F] in

theorem modulus_prod {ι : Type*} (s : Finset ι) (f : ι → F) :
    LocalField.modulus (∏ i ∈ s, f i) = ∏ i ∈ s, LocalField.modulus (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LocalField.modulus_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, LocalField.modulus_mul, ih]

theorem distribHaarChar_pi_eq_modulus {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → F) ≃ₗ[F] (ι → F)) :
    (distribHaarChar (ι → F) L : ℝ≥0) = LocalField.modulus (LinearEquiv.det L : F) := by
  rw [distribHaarChar_pi_eq, GroundTheory.LocalField.distribHaarChar_eq_modulus]

variable (β) in

abbrev leviDiag (μ : Fin n → ℤ) : levi F n β := ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩

theorem leviChart_leftModulus_diag (μ : Fin n → ℤ) :
    (leviChart β).leftModulus (leviDiag (F := F) β μ) =
      ∏ s : LeviIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq_modulus,
    det_eq_prod_of_apply _ (fun s => (uniformizer F : F) ^ μ s.1.1), modulus_prod]
  intro x s
  show (((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((leviCoord F n β).symm x : lieLevi F n β) : Matrix (Fin n) (Fin n) F)) s.1.1 s.1.2 = _
  rw [Cartan.coe_diagPow, Matrix.diagonal_mul]
  congr 1
  simp [leviCoord, s.2]

theorem parabolicChart_leftModulus_diag (μ : Fin n → ℤ) :
    (parabolicChart F n β).leftModulus (leviIncl (leviDiag (F := F) β μ)) =
      ∏ s : ParabolicIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq_modulus,
    det_eq_prod_of_apply _ (fun s => (uniformizer F : F) ^ μ s.1.1), modulus_prod]
  intro x s
  show (((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((parabolicCoord F n β).symm x : lieParabolic F n β) : Matrix (Fin n) (Fin n) F)) s.1.1 s.1.2 = _
  rw [Cartan.coe_diagPow, Matrix.diagonal_mul]
  congr 1
  simp [parabolicCoord, s.2]

theorem localField_modulus_eq_modulus {x : F} (hx : x ≠ 0) :
    LocalField.modulus x = Measures.modulus x := by
  rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, Measures.modulus_units,
    GroundTheory.LocalField.distribHaarChar_eq_modulus]

theorem modularCharacter_leviDiag (μ : Fin n → ℤ) :
    Measure.modularCharacter (leviIncl (leviDiag (F := F) β μ)) =
      ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
        LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) /
          LocalField.modulus ((uniformizer F : F) ^ μ s.1.2) := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  rw [modularCharacter_blockUpper_of_mem_borel' _ (diagPow_mem_borel μ)]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [leviIncl_coe, Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  rw [localField_modulus_eq_modulus (zpow_ne_zero _ hϖ),
    localField_modulus_eq_modulus (zpow_ne_zero _ hϖ)]

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_diagPow (μ : Fin n → ℤ) :
    LocalField.modulus ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      ∏ i, LocalField.modulus ((uniformizer F : F) ^ μ i) := by
  rw [Cartan.coe_diagPow, Matrix.det_diagonal, modulus_prod]

omit [MeasurableSpace F] [BorelSpace F] in

theorem prod_leviIndex_eq (f : Fin n → ℝ≥0) :
    ∏ s : LeviIndex n β, f s.1.1 = ∏ i, f i ^ blockSize β (blockOf β i) := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2)
    (by simp) (fun ij => f ij.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  congr 1
  rw [blockSize, Fintype.card_subtype]
  congr 1
  ext j
  simp [blockOf, Set.rangeFactorization, Subtype.ext_iff, eq_comm]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulus_diag (μ : Fin n → ℤ) :
    leviModulus β (leviDiag (F := F) β μ) =
      ∏ s : LeviIndex n β, LocalField.modulus ((uniformizer F : F) ^ μ s.1.1) := by
  classical
  have hblock : ∀ a, ((leviBlock F (leviDiag (F := F) β μ) a : GL (Fiber β a) F) :
      Matrix (Fiber β a) (Fiber β a) F).det = ∏ i : Fiber β a, (uniformizer F : F) ^ μ i.1 := by
    intro a
    rw [coe_leviBlock]
    have : blocks β F ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a =
        Matrix.diagonal fun i : Fiber β a => (uniformizer F : F) ^ μ i.1 := by
      ext i j
      simp only [blocks, Cartan.coe_diagPow, Matrix.diagonal_apply, Subtype.ext_iff]
    rw [this, Matrix.det_diagonal]
  rw [leviModulus, prod_leviIndex_eq (β := β) fun i => LocalField.modulus ((uniformizer F : F) ^ μ i)]
  simp_rw [hblock, modulus_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_fiberwise (blockOf β) fun i =>
    LocalField.modulus ((uniformizer F : F) ^ μ i) ^ blockSize β (blockOf β i)]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
  rw [i.2]

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in
theorem prod_subtype_eq_ite {M : Type*} [CommMonoid M] (P : Fin n × Fin n → Prop) [DecidablePred P]
    (g : Fin n × Fin n → M) :
    ∏ s : {ij : Fin n × Fin n // P ij}, g s.1 = ∏ ij, if P ij then g ij else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype (Finset.univ.filter P) (by simp) g).symm

omit [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] in

theorem prod_identity (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≠ 0) :
    ((∏ s : LeviIndex n β, t s.1.1) / ∏ s : ParabolicIndex n β, t s.1.1) ^ 2 *
      (∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, t s.1.1 / t s.1.2) * (∏ i, t i) ^ n =
      ∏ s : LeviIndex n β, t s.1.1 := by
  classical
  set A := ∏ ij : Fin n × Fin n, if β ij.1 = β ij.2 then t ij.1 else 1 with hAdef
  set U := ∏ ij : Fin n × Fin n, if β ij.1 < β ij.2 then t ij.1 else 1 with hUdef
  set L := ∏ ij : Fin n × Fin n, if β ij.2 < β ij.1 then t ij.1 else 1 with hLdef
  have hA : ∏ s : LeviIndex n β, t s.1.1 = A :=
    prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 = β ij.2) fun ij => t ij.1
  have hP : ∏ s : ParabolicIndex n β, t s.1.1 = A * U := by
    rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1) fun ij => t ij.1,
      hAdef, hUdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have hU : ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, t s.1.1 / t s.1.2 = U / L := by
    rw [prod_subtype_eq_ite (fun ij : Fin n × Fin n => β ij.1 < β ij.2) fun ij => t ij.1 / t ij.2]
    have hswap : L = ∏ ij : Fin n × Fin n, if β ij.1 < β ij.2 then t ij.2 else 1 :=
      Fintype.prod_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ fun ij => rfl
    rw [hswap, hUdef, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    split_ifs <;> simp
  have hall : (∏ i, t i) ^ n = A * U * L := by
    have : (∏ i, t i) ^ n = ∏ ij : Fin n × Fin n, t ij.1 := by
      rw [Fintype.prod_prod_type, ← Finset.prod_pow]
      simp
    rw [this, hAdef, hUdef, hLdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ij _ => ?_
    rcases lt_trichotomy (β ij.1) (β ij.2) with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  have hne : ∀ P : Fin n × Fin n → Prop, ∀ [DecidablePred P],
      (∏ ij : Fin n × Fin n, if P ij then t ij.1 else 1) ≠ 0 := fun P _ =>
    Finset.prod_ne_zero_iff.2 fun ij _ => by split_ifs <;> simp [ht]
  have hA0 : A ≠ 0 := hne _
  have hU0 : U ≠ 0 := hne _
  have hL0 : L ≠ 0 := hne _
  rw [hA, hP, hU, hall]
  field_simp

variable (β) in

def leviAbsDet : levi F n β →* ℝ≥0 where
  toFun m := LocalField.modulus (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det)
  map_one' := by simp [LocalField.modulus_one]
  map_mul' m m' := by simp [Matrix.det_mul, LocalField.modulus_mul]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviAbsDet_apply (m : levi F n β) :
    leviAbsDet β m = LocalField.modulus (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) :=
  rfl

variable (β) in

def leviModulusHom : levi F n β →* ℝ≥0 where
  toFun := leviModulus β
  map_one' := by
    simp only [leviModulus]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [coe_leviBlock, OneMemClass.coe_one, Units.val_one, blocks_one, Matrix.det_one,
      LocalField.modulus_one, one_pow]
  map_mul' m m' := by
    simp only [leviModulus, leviBlock_mul, Units.val_mul, Matrix.det_mul, LocalField.modulus_mul,
      mul_pow, Finset.prod_mul_distrib]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulusHom_apply (m : levi F n β) : leviModulusHom β m = leviModulus β m := rfl

omit [MeasurableSpace F] [BorelSpace F] in

theorem modulus_eq_one_of_ord {x : F} (hx : x ≠ 0) (h : LocalField.ord x = 0) :
    LocalField.modulus x = 1 :=
  LocalField.modulus_eq_one_iff.2 ⟨hx, h⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviAbsDet_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviAbsDet β k = 1 :=
  modulus_eq_one_of_ord (det_ne_zero _) (ordDet_of_mem_integralGL hk)

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviModulus_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviModulus β k = 1 := by
  refine Finset.prod_eq_one fun a _ => ?_
  rw [modulus_eq_one_of_ord (det_ne_zero_of_GL _) (blockOrd_of_mem_integralGL a hk), one_pow]

omit [MeasurableSpace F] [BorelSpace F] in
theorem leviRatio_of_mem_integralGL {k : levi F n β}
    (hk : (k : GL (Fin n) F) ∈ integralGL F n) : leviRatio β k = 1 :=
  eq_one_of_mem_compact (leviRatio β) continuous_leviRatio (isCompact_leviIntegral (F := F))
    (Subgroup.mem_subgroupOf.2 hk)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem hom_cartan (f : levi F n β →* ℝ≥0)
    (hf : ∀ k : levi F n β, (k : GL (Fin n) F) ∈ integralGL F n → f k = 1) {k₁ k₂ : levi F n β}
    (h₁ : (k₁ : GL (Fin n) F) ∈ integralGL F n) (h₂ : (k₂ : GL (Fin n) F) ∈ integralGL F n)
    (d : levi F n β) : f (k₁ * d * k₂) = f d := by
  rw [map_mul, map_mul, hf k₁ h₁, hf k₂ h₂, one_mul, mul_one]

theorem leviRatio_sq_mul_modular_mul_det (m : levi F n β) :
    leviRatio β m ^ 2 * Measure.modularCharacter (leviIncl m) * leviAbsDet β m ^ n =
      leviModulus β m := by
  obtain ⟨μ, k₁, hk₁, k₂, hk₂, hm⟩ := exists_eq_mul_diagPow_mul_levi m.2
  have e : m = ⟨k₁, hk₁.1⟩ * leviDiag (F := F) β μ * ⟨k₂, hk₂.1⟩ := Subtype.ext hm
  have h1 := hom_cartan (leviRatio β) (fun k hk => leviRatio_of_mem_integralGL hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h2 := hom_cartan (Measure.modularCharacter.comp leviIncl)
    (fun k hk => modularCharacter_eq_one_of_mem_integralGL _ hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h3 := hom_cartan (leviAbsDet β) (fun k hk => leviAbsDet_of_mem_integralGL hk) (k₁ := ⟨k₁, hk₁.1⟩)
    (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  have h4 := hom_cartan (leviModulusHom β) (fun k hk => leviModulus_of_mem_integralGL hk)
    (k₁ := ⟨k₁, hk₁.1⟩) (k₂ := ⟨k₂, hk₂.1⟩) hk₁.2 hk₂.2 (leviDiag (F := F) β μ)
  simp only [MonoidHom.coe_comp, Function.comp_apply, leviModulusHom_apply] at h2 h4
  rw [e, h1, h2, h3, h4, leviRatio_apply, leviChart_leftModulus_diag,
    parabolicChart_leftModulus_diag, modularCharacter_leviDiag, leviAbsDet_apply,
    modulus_det_diagPow, leviModulus_diag]
  exact prod_identity (fun i => LocalField.modulus ((uniformizer F : F) ^ μ i)) fun i =>
    LocalField.modulus_ne_zero (zpow_ne_zero _ (Cartan.uniformizer_ne_zero F))

end GodementJacquet

end GroundTheory.Automorphic
