import Mathlib
import GroundTheory.ProfiniteCohomology.TorsionDualDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section LocallyConstantHom

variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]

def locallyConstantHom : AddSubgroup (Additive G →+ M) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := by
    change IsLocallyConstant fun g : G => (0 : Additive G →+ M) (Additive.ofMul g)
    exact IsLocallyConstant.const (0 : M)
  add_mem' {χ ψ} hχ hψ := by
    change IsLocallyConstant fun g : G => (χ + ψ) (Additive.ofMul g)
    exact IsLocallyConstant.add hχ hψ
  neg_mem' {χ} hχ := by
    change IsLocallyConstant fun g : G => (-χ) (Additive.ofMul g)
    exact IsLocallyConstant.neg hχ

def locallyConstantHomQZEquiv : locallyConstantHom G (AddCircle (1 : ℚ)) ≃+ (Additive G →ₜ+ QZ) where
  toFun χ :=
    { toAddMonoidHom := QZ.toAddCircle.symm.toAddMonoidHom.comp χ.1
      continuous_toFun := (IsLocallyConstant.iff_continuous _).1 χ.2 }
  invFun χ := ⟨QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom,
    (IsLocallyConstant.iff_continuous (fun x : Additive G => χ x)).2 χ.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {G} in
@[simp]
theorem locallyConstantHomQZEquiv_apply (χ : locallyConstantHom G (AddCircle (1 : ℚ)))
    (g : Additive G) :
    locallyConstantHomQZEquiv G χ g = QZ.toAddCircle.symm (χ.1 g) :=
  rfl

end LocallyConstantHom

end GroundTheory.ProfCoh
