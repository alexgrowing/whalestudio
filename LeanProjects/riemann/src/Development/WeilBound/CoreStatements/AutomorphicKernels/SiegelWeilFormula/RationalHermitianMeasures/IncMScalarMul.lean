import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ExistsNeZeroOfMap

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigR_eq (z : AF F ⊗[F] E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem incM_scalar_mul {k p : ℕ} (η : E) (M : Matrix (Fin k) (Fin p) (AE F E)) :
    incM F (Matrix.scalar (Fin k) η) * M = inclR (F := F) (AF F) η • M := by
  rw [Matrix.smul_eq_diagonal_mul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [incM, Matrix.scalar_apply, h]

theorem inclR_inv_mul {η : E} (hne : η ≠ 0) : inclR (F := F) (AF F) η⁻¹ * inclR (F := F) (AF F) η = 1 := by
  rw [← map_mul, inv_mul_cancel₀ hne, map_one]

section HOf

variable {d : SD σ} {η : E} (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)

theorem hOf_val (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) (β : nA σ d.Y d.b) :
    ((hOf β).1 : Mx F E d.n d.n) = -(inclR (F := F) (AF F) η⁻¹ • (β.1)ᵀ) := by
  ext a b
  have h := congrFun (congrFun (hof β) b) a
  rw [incM_scalar_mul] at h
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h ⊢
  linear_combination inclR (F := F) (AF F) η⁻¹ * h - ((hOf β).1 a b) * inclR_inv_mul (F := F) hne

theorem inv_mem (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) :
    (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)) ∈ nA σ d.Y d.b := by
  have hσ := sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hb⟩, -⟩ := d.ok.frame
  have hrel := eta_sign d herm hb
  rw [mem_nA_iff hσ hb]
  have hS : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (S.1 b a) = S.1 a b := S.2
  have h1 : ∀ a b, cA σ (S.1 b a) = S.1 a b := fun a b => by rw [← sigR_eq]; exact hS a b
  have h2 : cA σ (inclR (F := F) (AF F) η) = -(((ε : ℤ) : AE F E)) * inclR (F := F) (AF F) η := by
    rw [cA_inclR', hrel, map_mul, map_neg, inclR_int]
  show (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ))ᵀ =
    -((((ε : ℤ) : AE F E)) • (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)).map (cA σ))
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_neg, map_mul,
    h1, h2]
  linear_combination (inclR (F := F) (AF F) η * S.1 a b) * eps_sq (F := F) (E := E) ε

def hEq (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    nA σ d.Y d.b ≃ₜ+ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n where
  toFun := hOf
  invFun S := ⟨-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ), inv_mem herm S⟩
  left_inv β := by
    apply Subtype.ext
    show -(inclR (F := F) (AF F) η • ((hOf β).1 : Mx F E d.n d.n)ᵀ) = β.1
    rw [hof β, incM_scalar_mul]
  right_inv S := by
    apply Subtype.ext
    rw [hOf_val hOf hne hof]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (S.1 a b) * inclR_inv_mul (F := F) hne
  map_add' β γ := by
    apply Subtype.ext
    show ((hOf (β + γ)).1 : Mx F E d.n d.n) = (hOf β).1 + (hOf γ).1
    rw [hOf_val hOf hne hof, hOf_val hOf hne hof, hOf_val hOf hne hof]
    ext a b
    simp only [AddSubgroup.coe_add, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    ring
  continuous_toFun := by
    apply continuous_induced_rng.2
    have hc : Continuous fun β : nA σ d.Y d.b => -(inclR (F := F) (AF F) η⁻¹ • (β.1 : Mx F E d.n d.n)ᵀ) :=
      (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
    exact hc.congr fun β => (hOf_val hOf hne hof β).symm
  continuous_invFun := by
    apply continuous_induced_rng.2
    show Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n => -(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)
    exact (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg

end HOf

end PositivityTheory.SiegelWeilFormula.MeasD

end
