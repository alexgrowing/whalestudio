import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN

noncomputable section

namespace MassDataMassesW.SplitW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]

abbrev q1 : (R1 × R2) ⊗[F] E →+* R1 ⊗[F] E := tensMap (E := E) (AlgHom.fst F R1 R2)

abbrev q2 : (R1 × R2) ⊗[F] E →+* R2 ⊗[F] E := tensMap (E := E) (AlgHom.snd F R1 R2)

def qq : (R1 × R2) ⊗[F] E →+* (R1 ⊗[F] E) × (R2 ⊗[F] E) := RingHom.prod (q1 R1 R2) (q2 R1 R2)

theorem prodFirstProjection_smul (c : R1 × R2) (z : (R1 × R2) ⊗[F] E) : q1 R1 R2 (c • z) = c.1 • q1 R1 R2 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem second_factor_proj_smul (c : R1 × R2) (z : (R1 × R2) ⊗[F] E) : q2 R1 R2 (c • z) = c.2 • q2 R1 R2 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem prodLeft_apply (z : (R1 × R2) ⊗[F] E) :
    TensorProduct.prodLeft F F R1 R2 E z = qq R1 R2 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.prodLeft_tmul]
    simp [qq, tensMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem qq_bijective : Function.Bijective (qq (F := F) (E := E) R1 R2) := by
  have h : (qq (F := F) (E := E) R1 R2 : (R1 × R2) ⊗[F] E → (R1 ⊗[F] E) × (R2 ⊗[F] E)) =
      TensorProduct.prodLeft F F R1 R2 E := funext fun z => (prodLeft_apply R1 R2 z).symm
  rw [h]
  exact (TensorProduct.prodLeft F F R1 R2 E).bijective

def QQ : (R1 × R2) ⊗[F] E ≃+* (R1 ⊗[F] E) × (R2 ⊗[F] E) := RingEquiv.ofBijective _ (qq_bijective R1 R2)

theorem QQ_apply (z : (R1 × R2) ⊗[F] E) : QQ R1 R2 z = (q1 R1 R2 z, q2 R1 R2 z) := by
  rfl

theorem first_factor_proj_equiv_symm (p : (R1 ⊗[F] E) × (R2 ⊗[F] E)) : q1 R1 R2 ((QQ R1 R2).symm p) = p.1 := by
  have h := QQ_apply R1 R2 ((QQ R1 R2).symm p)
  rw [RingEquiv.apply_symm_apply] at h
  exact (congrArg Prod.fst h).symm

theorem second_factor_proj_equiv_symm (p : (R1 ⊗[F] E) × (R2 ⊗[F] E)) : q2 R1 R2 ((QQ R1 R2).symm p) = p.2 := by
  have h := QQ_apply R1 R2 ((QQ R1 R2).symm p)
  rw [RingEquiv.apply_symm_apply] at h
  exact (congrArg Prod.snd h).symm

def j1 (x : R1 ⊗[F] E) : (R1 × R2) ⊗[F] E := (QQ R1 R2).symm (x, 0)

def j2 (y : R2 ⊗[F] E) : (R1 × R2) ⊗[F] E := (QQ R1 R2).symm (0, y)

theorem first_factor_incl_smul (a : R1) (x : R1 ⊗[F] E) :
    j1 R1 R2 (a • x) = ((a, 1) : R1 × R2) • j1 R1 R2 x := by
  apply (QQ R1 R2).injective
  rw [QQ_apply, QQ_apply, prodFirstProjection_smul, second_factor_proj_smul]
  simp only [j1, first_factor_proj_equiv_symm, second_factor_proj_equiv_symm, smul_zero]

theorem second_factor_incl_smul (b : R2) (y : R2 ⊗[F] E) :
    j2 R1 R2 (b • y) = ((1, b) : R1 × R2) • j2 R1 R2 y := by
  apply (QQ R1 R2).injective
  rw [QQ_apply, QQ_apply, prodFirstProjection_smul, second_factor_proj_smul]
  simp only [j2, first_factor_proj_equiv_symm, second_factor_proj_equiv_symm, smul_zero]

theorem QQ_symm_eq_add (p : (R1 ⊗[F] E) × (R2 ⊗[F] E)) :
    (QQ R1 R2).symm p = j1 R1 R2 p.1 + j2 R1 R2 p.2 := by
  rw [j1, j2, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

section Top

variable [TopologicalSpace R1] [TopologicalSpace R2]

instance isModTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance ctsSMulTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    ContinuousSMul R (R ⊗[F] E) := ModuleTopology.continuousSMul R (R ⊗[F] E)

instance ctsAddTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    ContinuousAdd (R ⊗[F] E) := ModuleTopology.continuousAdd R (R ⊗[F] E)

private theorem continuous_moduleTopology_of_semilinear {R S M N : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [tN : TopologicalSpace N]
    [ContinuousSMul S N] [ContinuousAdd N] (g : R → S) (hg : Continuous g) (f : M →+ N)
    (hf : ∀ (a : R) (x : M), f (a • x) = g a • f x) :
    @Continuous M N (moduleTopology R M) tN f := by
  letI t : TopologicalSpace M := TopologicalSpace.induced f tN
  have h1 : @ContinuousSMul R M _ _ t := by
    constructor
    rw [continuous_induced_rng]
    have e : (f ∘ fun p : R × M => p.1 • p.2) = fun p : R × M => g p.1 • f p.2 := funext fun p => hf p.1 p.2
    rw [e]
    exact (hg.comp continuous_fst).smul (continuous_induced_dom.comp continuous_snd)
  have h2 : @ContinuousAdd M t _ := by
    constructor
    rw [continuous_induced_rng]
    have e : (f ∘ fun p : M × M => p.1 + p.2) = fun p : M × M => f p.1 + f p.2 := funext fun p => map_add f _ _
    rw [e]
    exact (continuous_induced_dom.comp continuous_fst).add (continuous_induced_dom.comp continuous_snd)
  rw [continuous_iff_le_induced]
  exact sInf_le ⟨h1, h2⟩

theorem continuous_first_factor_proj : Continuous (q1 (F := F) (E := E) R1 R2) := by
  exact continuous_moduleTopology_of_semilinear Prod.fst continuous_fst (q1 (F := F) (E := E) R1 R2).toAddMonoidHom (prodFirstProjection_smul R1 R2)

theorem continuous_second_factor_proj : Continuous (q2 (F := F) (E := E) R1 R2) := by
  exact continuous_moduleTopology_of_semilinear Prod.snd continuous_snd (q2 (F := F) (E := E) R1 R2).toAddMonoidHom (second_factor_proj_smul R1 R2)

theorem continuous_first_factor_incl : Continuous (j1 (F := F) (E := E) R1 R2) := by
  exact continuous_moduleTopology_of_semilinear (fun a : R1 => ((a, 1) : R1 × R2)) (by fun_prop)
    (AddMonoidHom.mk' (j1 (F := F) (E := E) R1 R2) fun x y => by
      rw [j1, j1, j1, ← map_add, Prod.mk_add_mk, add_zero])
    (first_factor_incl_smul R1 R2)

theorem continuous_second_factor_incl : Continuous (j2 (F := F) (E := E) R1 R2) := by
  exact continuous_moduleTopology_of_semilinear (fun b : R2 => ((1, b) : R1 × R2)) (by fun_prop)
    (AddMonoidHom.mk' (j2 (F := F) (E := E) R1 R2) fun x y => by
      rw [j2, j2, j2, ← map_add, Prod.mk_add_mk, add_zero])
    (second_factor_incl_smul R1 R2)

theorem continuous_QQ_symm : Continuous (QQ (F := F) (E := E) R1 R2).symm := by
  have h : ⇑(QQ (F := F) (E := E) R1 R2).symm = fun p => j1 R1 R2 p.1 + j2 R1 R2 p.2 :=
    funext (QQ_symm_eq_add R1 R2)
  rw [h]
  exact ((continuous_first_factor_incl R1 R2).comp continuous_fst).add ((continuous_second_factor_incl R1 R2).comp continuous_snd)

end Top

end Tens

end MassDataMassesW.SplitW
