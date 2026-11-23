import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.trPair :
    ∀ (k : Type) [Field k] (n : ℕ) (g g' P : GL (Fin n) k) (μ : kˣ), (g : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (g' : Matrix (Fin n) (Fin n) k) = (μ : k) • (P : Matrix (Fin n) (Fin n) k) → Ga.tr g' = μ * Ga.tr g⁻¹ := by
  intro k _ n g g' P μ h
  set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k)
  set Ai : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set B : Matrix (Fin n) (Fin n) k := (g' : Matrix (Fin n) (Fin n) k)
  set M : Matrix (Fin n) (Fin n) k := (P : Matrix (Fin n) (Fin n) k)
  set Mi : Matrix (Fin n) (Fin n) k := ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hA : A * Ai = 1 := g.mul_inv
  have hM : Mi * M = 1 := P.inv_mul
  have hM' : M * Mi = 1 := P.mul_inv
  have hB : B = Mi * Aiᵀ * (Aᵀ * M * B) := by
    have : Aiᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA, Matrix.transpose_one]
    calc B = Mi * M * B := by rw [hM, Matrix.one_mul]
      _ = Mi * (Aiᵀ * Aᵀ) * M * B := by rw [this, Matrix.mul_one]
      _ = Mi * Aiᵀ * (Aᵀ * M * B) := by simp only [Matrix.mul_assoc]
  show B.trace = μ * Ai.trace
  rw [hB, h, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hM', Matrix.one_mul, Matrix.trace_transpose]
