import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem crd_smulO (c : K.O) (y : B.A) : crd e b (c • y) = e (algebraMap K.O K.E c) • crd e b y := by
  rw [← crd_smul, algebraMap_smul]

theorem crd_zero : crd e b (0 : B.A) = 0 := by
  funext i; simp [crd]

theorem mem_lat_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q : GLw a w) (y : B.A) :
    y ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ i, Valued.v (((q⁻¹ : GLw a w).val *ᵥ crd e b y) i) ≤ 1 := by
  rw [latOf_eq]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [crd_ofCrd, ← col_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    | zero => intro i; simp [crd_zero]
    | add x z _ _ hx hz =>
      intro i
      rw [crd_add, Matrix.mulVec_add, Pi.add_apply]
      exact (Valued.v.map_add _ _).trans (max_le (hx i) (hz i))
    | smul c x _ hx =>
      intro i
      rw [crd_smulO, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_one' ((he _).1 ⟨c, rfl⟩) (hx i)
  · intro h
    choose c hc using fun j => (he (e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b y) j))).2 (by
      rw [RingEquiv.apply_symm_apply]; exact h j)
    have hy : y = ∑ j, c j • ofCrd e b (fun i => q.val i j) := by
      apply crd_injective e b
      rw [crd_sum]
      have h1 : crd e b y = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b y) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [h1]
      funext i
      simp only [crd_smulO, hc, RingEquiv.apply_symm_apply, crd_ofCrd, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_le_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q q' : GLw a w) :
    GlobalTheory.TwLat.lat e b q ≤ GlobalTheory.TwLat.lat e b q' ↔ ∀ i j, Valued.v ((q'⁻¹ * q : GLw a w).val i j) ≤ 1 := by
  constructor
  · intro hle i j
    have hm : ofCrd e b (fun i => q.val i j) ∈ GlobalTheory.TwLat.lat e b q := by
      rw [latOf_eq]; exact Submodule.subset_span ⟨j, rfl⟩
    have := (mem_lat_iff e b he q' _).1 (hle hm) i
    rw [crd_ofCrd, ← col_mul, ← Units.val_mul] at this
    exact this
  · intro h
    conv_lhs => rw [latOf_eq]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_lat_iff e b he, crd_ofCrd, ← col_mul, ← Units.val_mul]
    exact fun i => h i j

theorem lat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (q q' : GLw a w),
    GlobalTheory.TwLat.lat e b q = GlobalTheory.TwLat.lat e b q' ↔ q⁻¹ * q' ∈ GlobalTheory.LFun.KGL w a := by
  intro E _ _ _ w K e he a B b q q'
  rw [le_antisymm_iff, lat_le_iff e b he, lat_le_iff e b he, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff,
    _root_.mul_inv_rev, inv_inv]
  exact and_comm

end GlobalTheory.TwOrbLat
