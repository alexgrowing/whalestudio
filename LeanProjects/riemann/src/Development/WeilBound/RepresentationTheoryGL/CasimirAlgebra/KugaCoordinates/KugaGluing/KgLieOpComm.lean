import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCoordAtEmbOfNe

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def kgA (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _ + (-(σ / 2 : ℂ) * kgT X) • 1
  map_add' X Y := by rw [map_add, LinearMap.rTensor_add, map_add, mul_add, add_smul]; abel
  map_smul' c X := by
    have e1 : lieOp π (c • X) = (c : ℂ) • lieOp π X := by rw [map_smul, ← algebraMap_smul ℂ c]; rfl
    have e2 : kgT (c • X) = (c : ℂ) * kgT X := by rw [map_smul, Complex.real_smul]
    simp only [RingHom.id_apply]
    rw [e1, e2, LinearMap.rTensor_smul, ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))),
      show algebraMap ℝ ℂ c = (c : ℂ) from rfl]
    module

def kgR (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (Matrix.toLin' (Ξ.dmat X)).lTensor _ + ((σ / 2 : ℂ) * kgT X) • 1
  map_add' X Y := by rw [map_add, map_add, LinearMap.lTensor_add, map_add, mul_add, add_smul]; abel
  map_smul' c X := by
    have e1 : Ξ.dmat (c • X) = (c : ℂ) • Ξ.dmat X := by rw [map_smul, ← algebraMap_smul ℂ c]; rfl
    have e2 : kgT (c • X) = (c : ℂ) * kgT X := by rw [map_smul, Complex.real_smul]
    simp only [RingHom.id_apply]
    rw [e1, e2, map_smul, LinearMap.lTensor_smul, ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))),
      show algebraMap ℝ ℂ c = (c : ℂ) from rfl]
    module

variable (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ)

theorem kgA_apply (X : Lie E a) : kgA π Ξ σ X = (lieOp π X).rTensor _ + (-(σ / 2 : ℂ) * kgT X) • 1 := rfl

theorem kgR_apply (X : Lie E a) :
    kgR π Ξ σ X = (Matrix.toLin' (Ξ.dmat X)).lTensor _ + ((σ / 2 : ℂ) * kgT X) • 1 := rfl

theorem kgA_add_kgR (X : Lie E a) : kgA π Ξ σ X + kgR π Ξ σ X = tensorLie π Ξ X := by
  rw [kgA_apply, kgR_apply]
  show _ = (lieOp π X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  rw [add_add_add_comm, ← add_smul, neg_mul, neg_add_cancel, zero_smul, add_zero]

theorem kg_lieOp_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    lieOp π (toL X) * lieOp π (toL Y) - lieOp π (toL Y) * lieOp π (toL X) = lieOp π (toL (X * Y - Y * X)) := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  have h := LinearMap.congr_fun (lie_comm (E := E) (a := a) (toL X) (toL Y)) φ.1
  have e : toL (X * Y - Y * X) =
      toL (Matrix.of (toL X) * Matrix.of (toL Y)) - toL (Matrix.of (toL Y) * Matrix.of (toL X)) := rfl
  rw [e, map_sub]
  exact h

theorem kgA_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    kgA π Ξ σ (toL X) * kgA π Ξ σ (toL Y) - kgA π Ξ σ (toL Y) * kgA π Ξ σ (toL X) = kgA π Ξ σ (toL (X * Y - Y * X)) := by
  have e : kgA π Ξ σ (toL (X * Y - Y * X)) = (lieOp π (toL (X * Y - Y * X))).rTensor _ := by
    rw [kgA_apply, kgT_comm]; simp
  rw [e, ← kg_lieOp_comm, LinearMap.rTensor_sub, LinearMap.rTensor_mul, LinearMap.rTensor_mul, kgA_apply, kgA_apply]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem kgR_comm (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    kgR π Ξ σ (toL X) * kgR π Ξ σ (toL Y) - kgR π Ξ σ (toL Y) * kgR π Ξ σ (toL X) = kgR π Ξ σ (toL (X * Y - Y * X)) := by
  have e : kgR π Ξ σ (toL (X * Y - Y * X)) = (Matrix.toLin' (Ξ.dmat (toL (X * Y - Y * X)))).lTensor _ := by
    rw [kgR_apply, kgT_comm]; simp
  rw [e, ← GlobalTheory.AlgInfChar.dmat_bracket,
    map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.lTensor_sub, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, LinearMap.lTensor_mul, LinearMap.lTensor_mul, kgR_apply, kgR_apply]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem kgA_kgR_comm (X Y : Lie E a) : Commute (kgA π Ξ σ X) (kgR π Ξ σ Y) := by
  have h : Commute ((lieOp π X).rTensor (Fin Ξ.d → ℂ) : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))
      ((Matrix.toLin' (Ξ.dmat Y)).lTensor π.V) := by
    show _ * _ = _ * _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [kgA_apply, kgR_apply]
  refine Commute.add_left ?_ ?_
  · refine Commute.add_right h ?_
    exact (Commute.one_right _).smul_right _
  · exact (Commute.one_left _).smul_left _

theorem cx_kgA (τ : E →+* ℂ) (i j : Fin a) :
    cx τ (kgA π Ξ σ) i j = (cx τ (lieOp π) i j).rTensor _ + (if i = j then -(σ / 2 : ℂ) else 0) • 1 := by
  have h := cx_kgT (E := E) (a := a) τ i j
  have e : (if i = j then -(σ / 2 : ℂ) else 0) = -(σ / 2 : ℂ) * cx τ (kgT (E := E) (a := a)) i j := by
    rw [h]; split_ifs <;> simp
  rw [e]
  simp only [cx, kgA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_smul, smul_eq_mul]
  module

theorem cx_kgR (τ : E →+* ℂ) (i j : Fin a) :
    cx τ (kgR π Ξ σ) i j = (Matrix.toLin' (cx τ Ξ.dmat i j)).lTensor _ + (if i = j then (σ / 2 : ℂ) else 0) • 1 := by
  have h := cx_kgT (E := E) (a := a) τ i j
  have e : (if i = j then (σ / 2 : ℂ) else 0) = (σ / 2 : ℂ) * cx τ (kgT (E := E) (a := a)) i j := by
    rw [h]; split_ifs <;> simp
  rw [e]
  simp only [cx, kgR_apply, map_sub, map_smul, LinearMap.lTensor_sub, LinearMap.lTensor_smul, smul_eq_mul]
  module

end
end PositivityTheory.Rg.Cz
