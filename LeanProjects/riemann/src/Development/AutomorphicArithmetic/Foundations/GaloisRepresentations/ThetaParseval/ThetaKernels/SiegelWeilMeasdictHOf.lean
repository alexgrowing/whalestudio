import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.IncMScalarMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictSign

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section HOf
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {η : E} (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
theorem hOf_val_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) (β : nA σ d.Y d.b) :
    ((hOf β).1 : Mx F E d.n d.n) = -(inclR (F := F) (AF F) η⁻¹ • (β.1)ᵀ) := by
  ext a b
  have h := congrFun (congrFun (hof β) b) a
  rw [incM_scalar_mul] at h
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h ⊢
  linear_combination inclR (F := F) (AF F) η⁻¹ * h - ((hOf β).1 a b) * inclR_inv_mul (F := F) hne
theorem inv_mem_k (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) :
    (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)) ∈ nA σ d.Y d.b := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hb⟩, -⟩ := d.ok.frame
  have hrel := _root_.PositivityTheory.SiegelWeilFormula.MeasD.eta_sign_k d herm hb
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
def hEq_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    nA σ d.Y d.b ≃ₜ+ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n where
  toFun := hOf
  invFun S := ⟨-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ), _root_.PositivityTheory.SiegelWeilFormula.MeasD.inv_mem_k herm S⟩
  left_inv β := by
    apply Subtype.ext
    show -(inclR (F := F) (AF F) η • ((hOf β).1 : Mx F E d.n d.n)ᵀ) = β.1
    rw [hof β, incM_scalar_mul]
  right_inv S := by
    apply Subtype.ext
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (S.1 a b) * inclR_inv_mul (F := F) hne
  map_add' β γ := by
    apply Subtype.ext
    show ((hOf (β + γ)).1 : Mx F E d.n d.n) = (hOf β).1 + (hOf γ).1
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [AddSubgroup.coe_add, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    ring
  continuous_toFun := by
    apply continuous_induced_rng.2
    have hc : Continuous fun β : nA σ d.Y d.b => -(inclR (F := F) (AF F) η⁻¹ • (β.1 : Mx F E d.n d.n)ᵀ) :=
      (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
    exact hc.congr fun β => (_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof β).symm
  continuous_invFun := by
    apply continuous_induced_rng.2
    show Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n => -(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)
    exact (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
end HOf
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
