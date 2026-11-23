import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd

namespace GlobalTheory.CompanionTheory.BZShell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

variable (k d V) in

def SchF : Submodule ℂ ((Fin d → k) → V) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' := fun c f hf => ⟨hf.1.comp (fun v => c • v), hf.2.comp_left (smul_zero c)⟩

theorem continuous_mulVec (g : GL (Fin d) k) :
    Continuous fun y : Fin d → k => (g : Matrix (Fin d) (Fin d) k).mulVec y := by
  exact Continuous.matrix_mulVec continuous_const continuous_id

def glHomeo (g : GL (Fin d) k) : (Fin d → k) ≃ₜ (Fin d → k) where
  toFun y := (g : Matrix (Fin d) (Fin d) k).mulVec y
  invFun y := ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y
  left_inv y := by
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv y := by
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  continuous_toFun := continuous_mulVec g
  continuous_invFun := continuous_mulVec g⁻¹

def shiftF (x : Fin d → k) : SchF k d V →ₗ[ℂ] SchF k d V where
  toFun f := ⟨fun y => f.1 (y + x), f.2.1.comp_continuous (continuous_id.add continuous_const),
    f.2.2.comp_homeomorph (Homeomorph.addRight x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def actF (X : Representation ℂ (GL (Fin d) k) V) (g : GL (Fin d) k) : SchF k d V →ₗ[ℂ] SchF k d V where
  toFun f := ⟨fun y => X g (f.1 ((glHomeo g).symm y)),
    (f.2.1.comp_continuous (glHomeo g).symm.continuous).comp (X g),
    (f.2.2.comp_homeomorph (glHomeo g).symm).comp_left (map_zero (X g))⟩
  map_add' f f' := Subtype.ext (funext fun y => map_add (X g) _ _)
  map_smul' c f := Subtype.ext (funext fun y => map_smul (X g) c _)

theorem shiftF_apply (x y : Fin d → k) (f : SchF k d V) : (shiftF x f).1 y = f.1 (y + x) := rfl

theorem actF_apply (X : Representation ℂ (GL (Fin d) k) V) (g : GL (Fin d) k) (f : SchF k d V) (y : Fin d → k) :
    (actF X g f).1 y = X g (f.1 (((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)) := rfl

theorem size_eq (m : ℕ) : (m + 1) + (m + 1) = ((m + 1) + m) + 1 := by omega

def Rm (ψ : AddChar k Circle) {m : ℕ} (π₁ π₂ : GRep k (m + 1)) : MRep k (m + 1) :=
  iterN ψ m (gres ((π₁.prod π₂).cast (size_eq m)))

def gOf {m : ℕ} (σ : IrrRep (GL (Fin (m + 1)) k)) : GRep k (m + 1) := ⟨σ.V, σ.ρ⟩

def gDual {m : ℕ} (σ : IrrRep (GL (Fin (m + 1)) k)) : GRep k (m + 1) := ⟨smoothPart σ.ρ.dual, contra σ.ρ⟩

end GlobalTheory.CompanionTheory.BZShell

end
