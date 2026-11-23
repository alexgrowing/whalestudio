import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolFib

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_orth_of {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (x : (VS D).V) (hx : ∀ i, (VS D).hT (F.e i) x = 0) :
    x ∈ orth (VS D) F.X := by
  unfold orth
  refine Submodule.mem_iInf _ |>.2 fun y => Submodule.mem_iInf _ |>.2 fun hy => ?_
  rw [LinearMap.mem_ker]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
  | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]

theorem orth_e {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (x : (VS D).V) (hx : x ∈ orth (VS D) F.X) (i : Fin D.R.rS) :
    (VS D).hT (F.e i) x = 0 := by
  unfold orth at hx
  have h := (Submodule.mem_iInf _ |>.1 hx) (F.e i)
  have h2 := (Submodule.mem_iInf _ |>.1 h) (Submodule.subset_span ⟨i, rfl⟩)
  exact LinearMap.mem_ker.1 h2

theorem img_quot (L a₁ a₂ : MatR D) (hL : IsUnit L.det) (ha₁ : IsUnit a₁.det) (x₁ x₂ : GLR D)
    (hx₁ : (x₁ : MatR D) = L⁻¹ * a₁ * L) (hx₂ : (x₂ : MatR D) = L⁻¹ * a₂ * L) :
    ((x₁⁻¹ * x₂ : GLR D) : MatR D) = L⁻¹ * (a₂.conjTranspose * (a₁.conjTranspose)⁻¹).conjTranspose * L := by
  have hinv : ((x₁⁻¹ : GLR D) : MatR D) = L⁻¹ * a₁⁻¹ * L := by
    rw [Matrix.coe_units_inv, hx₁]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * a₁⁻¹ * L * (L⁻¹ * a₁ * L) = L⁻¹ * (a₁⁻¹ * (L * L⁻¹) * a₁) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one, Matrix.nonsing_inv_mul _ ha₁, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hL]
  rw [Units.val_mul, hinv, hx₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc L⁻¹ * a₁⁻¹ * L * (L⁻¹ * a₂ * L) = L⁻¹ * a₁⁻¹ * (L * L⁻¹) * a₂ * L := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem act_quot (f : Fin (D.R.rS + 1) → (VS D).V) (t m₁ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (V₁ V₂ : MatR D)
    (hV₁ : IsUpUni V₁) (h₁ : ∀ b, m₁ (f b) = ∑ c, V₁ c b • f c) (h₂ : ∀ b, m₂ (f b) = ∑ c, V₂ c b • f c)
    (ht : ∀ b, t (m₁ (f b)) = m₂ (f b)) (b : Fin (D.R.rS + 1)) : t (f b) = ∑ c, (V₂ * V₁⁻¹) c b • f c := by
  have e : t = t * m₁ * m₁⁻¹ := (mul_inv_cancel_right t m₁).symm
  rw [e]
  exact act_mul f (t * m₁) m₁⁻¹ V₂ V₁⁻¹ (fun b => by show t (m₁ (f b)) = _; rw [ht, h₂]) (act_inv' f m₁ V₁ hV₁ h₁) b

end Formalism.L2.SG.Pf.ZsVolFib

end
