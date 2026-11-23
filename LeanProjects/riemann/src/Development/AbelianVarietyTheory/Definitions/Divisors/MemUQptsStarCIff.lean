import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIntMulIntegral

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

abbrev Datum.VQ : Type := ℚ ⊗[ℤ] D.La

instance Datum.finVQ : FiniteDimensional ℚ D.VQ := by
  haveI := D.finLa; infer_instance

def Datum.actQ : D.O →+* Module.End ℚ D.VQ :=
  (Module.End.baseChangeHom ℤ ℚ D.La).toRingHom.comp (Module.toModuleEnd ℤ (S := D.O) D.La)

theorem Datum.actQ_tmul (b : D.O) (q : ℚ) (x : D.La) : D.actQ b (q ⊗ₜ x) = q ⊗ₜ (b • x) := rfl

def Datum.EFQ : LinearMap.BilinForm ℚ D.VQ := D.EF.baseChange ℚ

theorem Datum.EFQ_tmul (q q' : ℚ) (x y : D.La) : D.EFQ (q ⊗ₜ x) (q' ⊗ₜ y) = (D.EF x y : ℚ) * (q * q') := by
  simp [Datum.EFQ, LinearMap.BilinForm.baseChange_tmul, mul_comm]

theorem Datum.EFQ_swap (x y : D.VQ) : D.EFQ y x = - D.EFQ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
  | tmul q x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
    | tmul q' y => rw [D.EFQ_tmul, D.EFQ_tmul, D.EF_swap x y]; push_cast; ring

theorem Datum.EFQ_actQ (b : D.O) (x y : D.VQ) : D.EFQ (D.actQ b x) y = D.EFQ x (D.actQ (D.star b).unop y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | tmul q x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add, h, h']
    | tmul q' y => rw [D.actQ_tmul, D.actQ_tmul, D.EFQ_tmul, D.EFQ_tmul, D.adj]

theorem Datum.exists_tmul (v : D.VQ) : ∃ (q : ℚ) (x : D.La), q ≠ 0 ∧ v = q ⊗ₜ x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q x =>
    by_cases h : q = 0
    · exact ⟨1, 0, one_ne_zero, by simp [h]⟩
    · exact ⟨q, x, h, rfl⟩
  | add v v' h h' =>
    obtain ⟨q, x, -, rfl⟩ := h
    obtain ⟨q', x', -, rfl⟩ := h'
    have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hd' : (q'.den : ℚ) ≠ 0 := by exact_mod_cast q'.den_ne_zero
    refine ⟨1 / (q.den * q'.den), (q.num * q'.den : ℤ) • x + (q'.num * q.den : ℤ) • x', by positivity, ?_⟩
    rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    congr 2
    · rw [zsmul_eq_mul]; push_cast; conv_lhs => rw [← Rat.num_div_den q]
      field_simp
    · rw [zsmul_eq_mul]; push_cast; conv_lhs => rw [← Rat.num_div_den q']
      field_simp

theorem Datum.eq_zero_of_EFQ {v : D.VQ} (h : ∀ w, D.EFQ v w = 0) : v = 0 := by
  obtain ⟨q, x, hq, rfl⟩ := D.exists_tmul v
  have hx : D.EF x = D.EF 0 := by
    ext y
    have := h (1 ⊗ₜ y)
    rw [D.EFQ_tmul, mul_one] at this
    have h2 : (D.EF x y : ℚ) = 0 := (mul_eq_zero.1 this).resolve_right hq
    simpa using h2
  rw [D.nondeg hx, TensorProduct.tmul_zero]

theorem Datum.EFQ_nondeg : D.EFQ.Nondegenerate :=
  ⟨fun _ h => D.eq_zero_of_EFQ h, fun v h => D.eq_zero_of_EFQ fun w => by rw [D.EFQ_swap, h, neg_zero]⟩

def Datum.adjE (g : Module.End ℚ D.VQ) : Module.End ℚ D.VQ := D.EFQ.leftAdjointOfNondegenerate D.EFQ_nondeg g

theorem Datum.EFQ_adjE_left (g : Module.End ℚ D.VQ) (x y : D.VQ) : D.EFQ (D.adjE g x) y = D.EFQ x (g y) :=
  D.EFQ.isAdjointPairLeftAdjointOfNondegenerate D.EFQ_nondeg g x y

theorem Datum.EFQ_adjE_right (g : Module.End ℚ D.VQ) (x y : D.VQ) : D.EFQ (g x) y = D.EFQ x (D.adjE g y) := by
  rw [D.EFQ_swap y, D.EFQ_swap (D.adjE g y), D.EFQ_adjE_left]

theorem Datum.end_ext {g h : Module.End ℚ D.VQ} (H : ∀ x y, D.EFQ (g x) y = D.EFQ (h x) y) : g = h := by
  refine LinearMap.ext fun x => sub_eq_zero.1 (D.eq_zero_of_EFQ fun y => ?_)
  rw [map_sub, LinearMap.sub_apply, H, sub_self]

theorem Datum.adjE_adjE (g : Module.End ℚ D.VQ) : D.adjE (D.adjE g) = g :=
  D.end_ext fun x y => by rw [D.EFQ_adjE_left, D.EFQ_adjE_right]

theorem Datum.adjE_mul (g h : Module.End ℚ D.VQ) : D.adjE (g * h) = D.adjE h * D.adjE g :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, Module.End.mul_apply]

theorem Datum.adjE_add (g h : Module.End ℚ D.VQ) : D.adjE (g + h) = D.adjE g + D.adjE h :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, LinearMap.add_apply, map_add]

theorem Datum.adjE_smul (q : ℚ) (g : Module.End ℚ D.VQ) : D.adjE (q • g) = q • D.adjE g :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, LinearMap.smul_apply, map_smul]

theorem Datum.adjE_one : D.adjE 1 = 1 :=
  D.end_ext fun x y => by simp only [D.EFQ_adjE_left, Module.End.one_apply]

theorem Datum.adjE_zero : D.adjE 0 = 0 :=
  D.end_ext fun x y => by simp [D.EFQ_adjE_left]

theorem Datum.adjE_actQ (b : D.O) : D.adjE (D.actQ b) = D.actQ (D.star b).unop :=
  D.end_ext fun x y => by rw [D.EFQ_adjE_left, D.EFQ_actQ, D.star_star]

def Datum.endO : Subalgebra ℚ (Module.End ℚ D.VQ) := Subalgebra.centralizer ℚ (Set.range D.actQ)

theorem Datum.mem_endO {g : Module.End ℚ D.VQ} : g ∈ D.endO ↔ ∀ b, D.actQ b * g = g * D.actQ b := by
  simp [Datum.endO, Subalgebra.mem_centralizer_iff]

theorem Datum.adjE_mem {g : Module.End ℚ D.VQ} (hg : g ∈ D.endO) : D.adjE g ∈ D.endO := by
  rw [D.mem_endO] at hg ⊢
  intro b
  have h := congrArg D.adjE (hg (D.star b).unop)
  rw [D.adjE_mul, D.adjE_mul, D.adjE_actQ, D.star_star] at h
  exact h.symm

def Datum.starC : D.endO →+* D.endOᵐᵒᵖ where
  toFun g := MulOpposite.op ⟨D.adjE g, D.adjE_mem g.2⟩
  map_one' := MulOpposite.unop_injective (Subtype.ext D.adjE_one)
  map_mul' g h := MulOpposite.unop_injective (Subtype.ext (D.adjE_mul g h))
  map_zero' := MulOpposite.unop_injective (Subtype.ext D.adjE_zero)
  map_add' g h := MulOpposite.unop_injective (Subtype.ext (D.adjE_add g h))

theorem Datum.coe_starC (g : D.endO) : (((D.starC g).unop : D.endO) : Module.End ℚ D.VQ) = D.adjE g := rfl

theorem Datum.starC_starC (g : D.endO) : (D.starC (D.starC g).unop).unop = g := Subtype.ext (D.adjE_adjE g)

def Datum.actInt : 𝓞 D.F →+* D.endO :=
  (D.actQ.comp (algebraMap (𝓞 D.F) D.O)).codRestrict D.endO fun c => D.mem_endO.2 fun b => by
    rw [RingHom.comp_apply, ← map_mul, ← map_mul, Algebra.commutes]

theorem Datum.coe_actInt (c : 𝓞 D.F) : (D.actInt c : Module.End ℚ D.VQ) = D.actQ (algebraMap (𝓞 D.F) D.O c) := rfl

def Datum.actFL : D.F →ₗ[ℚ] D.endO :=
  (integralBasis D.F).constr ℚ fun i => D.actInt (RingOfIntegers.basis D.F i)

theorem Datum.actFL_coe (c : 𝓞 D.F) : D.actFL (c : D.F) = D.actInt c := by
  have h : (D.actFL.restrictScalars ℤ).comp (algebraMap (𝓞 D.F) D.F).toIntAlgHom.toLinearMap =
      D.actInt.toIntAlgHom.toLinearMap := by
    refine (RingOfIntegers.basis D.F).ext fun i => ?_
    show D.actFL (algebraMap (𝓞 D.F) D.F (RingOfIntegers.basis D.F i)) = D.actInt _
    rw [← integralBasis_apply, Datum.actFL, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h c

def Datum.actF : D.F →ₐ[ℚ] D.endO :=
  AlgHom.ofLinearMap D.actFL (by simpa using D.actFL_coe 1) (by
    refine (LinearMap.map_mul_iff D.actFL).2 ?_
    refine (integralBasis D.F).ext fun i => (integralBasis D.F).ext fun j => ?_
    show D.actFL (integralBasis D.F i * integralBasis D.F j) = D.actFL (integralBasis D.F i) * D.actFL (integralBasis D.F j)
    rw [integralBasis_apply, integralBasis_apply, ← map_mul]
    exact (D.actFL_coe _).trans ((map_mul _ _ _).trans (by rw [← D.actFL_coe, ← D.actFL_coe])))

theorem Datum.actF_coe (c : 𝓞 D.F) : D.actF (c : D.F) = D.actInt c := D.actFL_coe c

theorem Datum.actF_comm (x : D.F) (g : D.endO) : D.actF x * g = g * D.actF x := by
  have h : (LinearMap.mulRight ℚ g).comp D.actFL = (LinearMap.mulLeft ℚ g).comp D.actFL := by
    refine (integralBasis D.F).ext fun i => ?_
    show D.actFL (integralBasis D.F i) * g = g * D.actFL (integralBasis D.F i)
    rw [integralBasis_apply]
    erw [D.actFL_coe]
    exact Subtype.ext (D.mem_endO.1 g.2 _)
  exact LinearMap.congr_fun h x

instance Datum.algebraF : Algebra D.F D.endO := D.actF.toRingHom.toAlgebra' D.actF_comm

theorem Datum.algebraMap_endO (x : D.F) : algebraMap D.F D.endO x = D.actF x := rfl

instance Datum.towerF : IsScalarTower ℚ D.F D.endO :=
  IsScalarTower.of_algebraMap_eq fun q => (D.actF.commutes q).symm

instance Datum.finEndO : FiniteDimensional D.F D.endO := Module.Finite.of_restrictScalars_finite ℚ D.F D.endO

theorem Datum.starC_algebraMap (x : D.F) :
    (D.starC (algebraMap D.F D.endO x)).unop = algebraMap D.F D.endO (IsCMField.complexConj D.F x) := by
  let L : D.endO →ₗ[ℚ] D.endO :=
    { toFun := fun g => (D.starC g).unop
      map_add' := fun g h => by rw [map_add, MulOpposite.unop_add]
      map_smul' := fun q g => Subtype.ext (D.adjE_smul q g) }
  have h : L.comp D.actFL = D.actFL.comp (GlobalTheory.LKTrip.conjQ D.F).toLinearMap := by
    refine (integralBasis D.F).ext fun i => ?_
    show (D.starC (D.actFL (integralBasis D.F i))).unop = D.actFL (IsCMField.complexConj D.F (integralBasis D.F i))
    rw [integralBasis_apply]
    erw [← D.bar_eq, D.actFL_coe, D.actFL_coe]
    apply Subtype.ext
    rw [D.coe_starC, D.coe_actInt, D.coe_actInt, D.adjE_actQ, D.star_F, MulOpposite.unop_op]
  exact LinearMap.congr_fun h x

theorem Datum.mem_UQpts_starC_iff (x : D.endOˣ × ℚˣ) :
    x ∈ GlobalTheory.LKTrip.UQpts D.starC ↔ ∀ v w : D.VQ,
      D.EFQ (((x.1 : D.endO) : Module.End ℚ D.VQ) v) (((x.1 : D.endO) : Module.End ℚ D.VQ) w) =
        (x.2 : ℚ) * D.EFQ v w := by
  obtain ⟨g, c⟩ := x
  rw [GlobalTheory.LKTrip.UQpts, GlobalTheory.LKTrip.mem_uGroup]
  have e : (g : D.endO) * (D.starC g).unop = algebraMap ℚ D.endO c ↔
      (D.starC g).unop * (g : D.endO) = algebraMap ℚ D.endO c := by
    constructor
    · intro h
      have : (D.starC g).unop = (g⁻¹ : D.endOˣ) * algebraMap ℚ D.endO c := by
        rw [← h, Units.inv_mul_cancel_left]
      rw [this, ← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]
    · intro h
      have : (D.starC g).unop = algebraMap ℚ D.endO c * (g⁻¹ : D.endOˣ) := by
        rw [← h, Units.mul_inv_cancel_right]
      rw [this, Algebra.commutes, ← mul_assoc, Units.mul_inv, one_mul]
  refine e.trans ⟨fun h v w => ?_, fun h => Subtype.ext (D.end_ext fun v w => ?_)⟩
  · have h' := congrArg (fun k : D.endO => D.EFQ ((k : Module.End ℚ D.VQ) v) w) h
    simpa [D.coe_starC, D.EFQ_adjE_left, Algebra.algebraMap_eq_smul_one] using h'
  · simpa [D.coe_starC, D.EFQ_adjE_left, Algebra.algebraMap_eq_smul_one] using h v w

example : ((1, 1) : D.endOˣ × ℚˣ) ∈ GlobalTheory.LKTrip.UQpts D.starC := (GlobalTheory.LKTrip.UQpts D.starC).one_mem

example (x : D.La) : ((algebraMap D.F D.endO (D.ω : D.F) : D.endO) : Module.End ℚ D.VQ) (1 ⊗ₜ x) =
    1 ⊗ₜ D.smulF D.ω x := by
  rw [D.algebraMap_endO, D.actF_coe]; rfl

end GlobalTheory.UPel.HT
