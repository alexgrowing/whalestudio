import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace GlobalTheory.ContraPair.Model

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def sc (χ : HChar E) (o : Op E a) : ℂ := ((opMul χ o : ℂˣ) : ℂ) * opTriv o + opAdd χ o

abbrev line (ha : a ≤ 1) (χ : HChar E) : CuspSub E a := (CuspSub.triv E ha).twist χ

theorem op_line (ha : a ≤ 1) (χ : HChar E) (o : Op E a) (φ : (line ha χ).V) : (line ha χ).op o φ = sc χ o • φ :=
  CuspSub.op_triv_twist ha χ o φ

def gen (ha : a ≤ 1) (χ : HChar E) : (line ha χ).V :=
  (CuspSub.triv E ha).toTwist χ ⟨oneFn E a, Submodule.mem_span_singleton_self _⟩

theorem gen_one (ha : a ≤ 1) (χ : HChar E) : (gen ha χ).1.1 1 = 1 := by
  change (1 : ℂ) * ((chiDet a χ 1 : ℂˣ) : ℂ) = 1
  simp

theorem eq_smul_gen (ha : a ≤ 1) (χ : HChar E) (φ : (line ha χ).V) : φ = φ.1.1 1 • gen ha χ := by
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := ((CuspSub.triv E ha).toTwist χ).surjective φ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  have e : (CuspSub.triv E ha).toTwist χ ⟨c • oneFn E a, hφ⟩ = c • gen ha χ := by
    rw [gen, ← map_smul]; rfl
  rw [e]
  congr 1
  change c = c * (gen ha χ).1.1 1
  rw [gen_one, mul_one]

def ev (π : CuspSub E a) : π.V →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp ((Sm E a).subtype.comp π.V.subtype)

theorem paired_line_iff (ha : a ≤ 1) (χ χ' : HChar E) (s : Op E a → Op E a) :
    Paired (line ha χ) (line ha χ') s ↔ (∀ k, sc χ (.fin k) * sc χ' (s (.fin k)) = 1) ∧
      (∀ k, sc χ (.cpt k) * sc χ' (s (.cpt k)) = 1) ∧ ∀ X, sc χ (.lie X) + sc χ' (s (.lie X)) = 0 := by
  constructor
  · rintro ⟨B, h1, -, h3, h4, h5⟩
    have h0 : B (gen ha χ) (gen ha χ') ≠ 0 := fun h => by
      have := h1 (gen ha χ) fun ψ => by rw [eq_smul_gen ha χ' ψ, map_smul, h, smul_zero]
      have h' := gen_one ha χ
      rw [this] at h'
      exact zero_ne_one h'
    refine ⟨fun k => ?_, fun k => ?_, fun X => ?_⟩
    · have := h3 k (gen ha χ) (gen ha χ')
      simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ h0 (by linear_combination this)
    · have := h4 k (gen ha χ) (gen ha χ')
      simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ h0 (by linear_combination this)
    · have := h5 X (gen ha χ) (gen ha χ')
      simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ h0 (by linear_combination this)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ (ev _) (ev _), fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
      fun k φ ψ => ?_, fun X φ ψ => ?_⟩
    · have : φ.1.1 1 * (gen ha χ').1.1 1 = 0 := h (gen ha χ')
      rw [gen_one, mul_one] at this
      rw [eq_smul_gen ha χ φ, this, zero_smul]
    · have : (gen ha χ).1.1 1 * ψ.1.1 1 = 0 := h (gen ha χ)
      rw [gen_one, one_mul] at this
      rw [eq_smul_gen ha χ' ψ, this, zero_smul]
    · simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (sc χ' _), h1, one_mul]
    · simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (sc χ' _), h2, one_mul]
    · simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← add_mul, h3, zero_mul]

omit [NumberField E] [IsTotallyComplex E] in

theorem toUnits_barK (k : Kinf E a) : Unitary.toUnits (barK k) = invT a (Cinf E) (Unitary.toUnits k) := Units.ext rfl

omit [NumberField E] [IsTotallyComplex E] in

theorem barK_apply (k : Kinf E a) (i j : Fin a) : (barK k).1 i j = star (k.1 i j) := rfl

theorem det_invT {R : Type} [CommRing R] (g : GL (Fin a) R) :
    GeneralLinearGroup.det (invT a R g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  exact Units.ext (Matrix.det_transpose _)

theorem sc_barK (χ : HChar E) (k : Kinf E a) : sc χ (.cpt k) * sc χ (.cpt (barK k)) = 1 := by
  simp only [sc, opMul, opTriv, opAdd, mul_one, add_zero, chiDet, MonoidHom.comp_apply, det_infGL, toUnits_barK,
    det_invT, map_inv]
  simp

theorem paired_invTOp (ha : a ≤ 1) (χ : HChar E) : Paired (line ha χ) (line ha χ) invTOp := by
  refine (paired_line_iff ha χ χ _).2 ⟨fun k => ?_, fun k => sc_barK χ k, fun X => ?_⟩
  · simp only [invTOp, sc, opMul, opTriv, opAdd, mul_one, add_zero, chiDet, MonoidHom.comp_apply, det_finGL,
      det_invT, map_inv]
    simp
  · simp only [invTOp, sc, opTriv, opAdd, mul_zero, zero_add]
    change _ + dchi χ (-(Matrix.of X)ᵀ).trace = 0
    rw [Matrix.trace_neg, Matrix.trace_transpose, map_neg, add_neg_cancel]

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem det_map' {R S : Type} [CommRing R] [CommRing S] (c : R →+* S) (k : GL (Fin a) R) :
    GeneralLinearGroup.det (GeneralLinearGroup.map c k) = Units.map c.toMonoidHom (GeneralLinearGroup.det k) :=
  by
  apply Units.ext
  rw [GlobalTheory.CuspRep.det_map]
  rfl

theorem sc_fin (μ : HChar L) (k : GL (Fin a) (Af L)) :
    sc μ (thetaOp (.fin k)) * sc μ (conjOp (.fin k)) = 1 := by
  simp only [thetaOp, conjOp, sc, opMul, opTriv, opAdd, mul_one, add_zero, chiDet, MonoidHom.comp_apply, det_finGL,
    det_thetaGL, map_inv, det_map']
  simp

theorem sc_cpt (μ : HChar L) (k : Kinf L a) :
    sc μ (thetaOp (.cpt k)) * sc μ (conjOp (.cpt k)) = 1 := by
  rw [← sc_barK μ k]
  simp only [thetaOp, conjOp, sc, opMul, map_mul, map_inv, mul_inv_cancel_comm, opTriv, opAdd]

theorem sc_lie (μ : HChar L) (X : Lie L a) :
    sc μ (thetaOp (.lie X)) + sc μ (conjOp (.lie X)) = 0 := by
  simp only [thetaOp, conjOp, sc, opTriv, opAdd, mul_zero, zero_add]
  change dchi μ (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)).trace + _ = 0
  rw [CG.trace_theta, map_neg, neg_add_eq_zero]
  congr 1
  simp [Matrix.trace]

theorem dualIsConjBy_line_iff (ha : a ≤ 1) (μ ψ : HChar L) :
    DualIsConjBy (line ha μ) ψ ↔ IsConjDualBy (line ha μ) ψ := by
  have h0 : IsConjDualBy (line ha μ) ψ ↔ ∀ o : Op L a, sc μ (thetaOp o) = sc (μ * ψ⁻¹) o := by
    rw [IsConjDualBy, ← CuspSub.twist_mul]
    constructor
    · rintro ⟨T, hT⟩ o
      have h := hT o (gen ha μ)
      rw [op_line, op_line, map_smul] at h
      refine smul_left_injective ℂ ((map_ne_zero_iff T T.injective).2 fun e => ?_) h
      have h' := gen_one ha μ
      rw [e] at h'
      exact zero_ne_one h'
    · intro h
      refine ⟨((CuspSub.triv L ha).toTwist μ).symm.trans ((CuspSub.triv L ha).toTwist _), fun o φ => ?_⟩
      rw [op_line, op_line, map_smul, h]
  rw [h0, DualIsConjBy, ← CuspSub.twist_mul, paired_line_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩ o
    cases o with
    | fin k => exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (h1 k)) ((sc_fin μ k).trans (h1 k).symm)
    | cpt k => exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (h2 k)) ((sc_cpt μ k).trans (h2 k).symm)
    | lie X => exact add_right_cancel ((sc_lie μ X).trans (h3 X).symm)
  · intro h
    exact ⟨fun k => h _ ▸ sc_fin μ k, fun k => h _ ▸ sc_cpt μ k, fun X => h _ ▸ sc_lie μ X⟩

theorem dualIsConj_line_iff (ha : a ≤ 1) (μ : HChar L) : DualIsConj (line ha μ) ↔ (line ha μ).IsCsd := by
  rw [← dualIsConjBy_one, dualIsConjBy_line_iff, isConjDualBy_one]

theorem polarizedPair_line_iff (ha : a ≤ 1) (μ : HChar L) (χ : HChar (maximalRealSubfield L)) :
    PolarizedPair (line ha μ) χ ↔ IsPolarized (line ha μ) χ :=
  ⟨fun h => ⟨h.sign, (dualIsConjBy_line_iff ha μ _).1 h.dual⟩, fun h => ⟨h.sign, (dualIsConjBy_line_iff ha μ _).2 h.dual⟩⟩

theorem dualIsConj_abs_iff (s : ℂ) : DualIsConj (line le_rfl (CuspRep.Model.absC L s)) ↔ s = 0 := by
  rw [dualIsConj_line_iff]
  exact CuspRep.Model.isCsd_absC s

theorem polarizedPair_triv : PolarizedPair (CuspSub.triv L (le_refl 1)) (quadChar L ^ 1) := by
  have h := (polarizedPair_line_iff (L := L) (le_refl 1) 1 (quadChar L ^ 1)).2
  rw [line, CuspSub.twist_one] at h
  exact h isPolarized_triv.1

theorem not_polarizedPair_one (π : CuspSub L 1) : ¬ PolarizedPair π 1 := fun h => by
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have h1 : (1 : ℂˣ) = (-1) ^ 1 := h.sign v
  have h2 := congrArg Units.val h1
  norm_num at h2

theorem polarizedPair_absPow (s : ℝ) : ∃ χ, PolarizedPair (line le_rfl (GlobalTheory.HeckeGal.Model.absPow L s)) χ := by
  have h : (CuspSub.triv L (le_refl 1)).IsCsd := by
    have h2 := (dualIsConj_line_iff (L := L) (le_refl 1) 1).1 (by
      refine (paired_line_iff _ _ _ _).2 ⟨fun k => ?_, fun k => sc_barK 1 k, fun X => ?_⟩
      · simp [sc, conjOp, opMul, opTriv, opAdd, chiDet]
      · have h0 : dchi (1 : HChar L) = 0 := fderiv_extZero (continuous_chiInf 1) fun z => by simp [chiInf]
        simp [sc, conjOp, opTriv, opAdd, h0])
    rwa [line, CuspSub.twist_one] at h2
  exact ⟨_, (polarizedPair_line_iff _ _ _).2 (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow h s)⟩

theorem dualIsConjBy_resReal (μ : HChar L) :
    DualIsConjBy (line le_rfl μ) (compNorm L (GlobalTheory.HeightCounting.Blocks.resReal μ)) := by
  have h := isPolarized_triv (E := L).1.dual
  rw [pow_one, compNorm_quadChar, isConjDualBy_one] at h
  exact (dualIsConjBy_line_iff _ _ _).2 (GlobalTheory.HeightCounting.Blocks.isConjDualBy_resReal h μ)

end GlobalTheory.ContraPair.Model

end
