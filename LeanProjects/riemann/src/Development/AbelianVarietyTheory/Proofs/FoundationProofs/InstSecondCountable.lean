import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable

open Formalism.BasicNotions Formalism.BasicNotions.TH Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolDS

variable {p q : ℕ}

abbrev PolB (p q : ℕ) : Type := MvPolynomial (Fin p × Fin q) ℂ

def InU (x : Mat p q) : Prop := xᴴ * Jm p q * x = Jm p q

def zOf (x : Mat p q) : Fin p × Fin q → ℂ := fun ij => (x.toBlocks₁₂ * (x.toBlocks₂₂)⁻¹) ij.1 ij.2

def Phi (k : ℕ) (P : PolB p q) (x : Mat p q) : ℂ :=
  (x.toBlocks₂₂.det)⁻¹ ^ k * MvPolynomial.eval (zOf x) P

def col (Z : Fin p × Fin q → ℂ) : Mat p q := Matrix.fromBlocks 1 (Matrix.of fun i j => Z (i, j)) 0 1

def Zm (p q : ℕ) : Matrix (Fin p) (Fin q) (PolB p q) := Matrix.of fun i j => MvPolynomial.X (i, j)

def cM (p q : ℕ) {m n : Type} (A : Matrix m n ℂ) : Matrix m n (PolB p q) := A.map MvPolynomial.C

def vf (Y : Mat p q) : Matrix (Fin p) (Fin q) (PolB p q) :=
  cM p q Y.toBlocks₁₁ * Zm p q + cM p q Y.toBlocks₁₂ - Zm p q * cM p q Y.toBlocks₂₁ * Zm p q - Zm p q * cM p q Y.toBlocks₂₂

def tau (Y : Mat p q) : PolB p q := Matrix.trace (cM p q Y.toBlocks₂₁ * Zm p q + cM p q Y.toBlocks₂₂)

theorem cM_add {m n : Type} (A B : Matrix m n ℂ) : cM p q (A + B) = cM p q A + cM p q B := by
  ext i j : 1; simp [cM]

theorem cM_smul {m n : Type} (c : ℂ) (A : Matrix m n ℂ) : cM p q (c • A) = c • cM p q A := by
  ext i j : 1; simp [cM, MvPolynomial.smul_eq_C_mul]

theorem vf_add (X Y : Mat p q) : vf (X + Y) = vf X + vf Y := by
  have h1 : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := rfl
  have h2 : (X + Y).toBlocks₁₂ = X.toBlocks₁₂ + Y.toBlocks₁₂ := rfl
  have h3 : (X + Y).toBlocks₂₁ = X.toBlocks₂₁ + Y.toBlocks₂₁ := rfl
  have h4 : (X + Y).toBlocks₂₂ = X.toBlocks₂₂ + Y.toBlocks₂₂ := rfl
  simp only [vf, h1, h2, h3, h4, cM_add, Matrix.add_mul, Matrix.mul_add]
  abel

theorem vf_smul (c : ℂ) (X : Mat p q) : vf (c • X) = c • vf X := by
  have h1 : (c • X).toBlocks₁₁ = c • X.toBlocks₁₁ := rfl
  have h2 : (c • X).toBlocks₁₂ = c • X.toBlocks₁₂ := rfl
  have h3 : (c • X).toBlocks₂₁ = c • X.toBlocks₂₁ := rfl
  have h4 : (c • X).toBlocks₂₂ = c • X.toBlocks₂₂ := rfl
  simp only [vf, h1, h2, h3, h4, cM_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub]

theorem tau_add (X Y : Mat p q) : tau (X + Y) = tau X + tau Y := by
  have h3 : (X + Y).toBlocks₂₁ = X.toBlocks₂₁ + Y.toBlocks₂₁ := rfl
  have h4 : (X + Y).toBlocks₂₂ = X.toBlocks₂₂ + Y.toBlocks₂₂ := rfl
  simp only [tau, h3, h4, cM_add, Matrix.add_mul, Matrix.trace_add]
  abel

theorem tau_smul (c : ℂ) (X : Mat p q) : tau (c • X) = c • tau X := by
  have h3 : (c • X).toBlocks₂₁ = c • X.toBlocks₂₁ := rfl
  have h4 : (c • X).toBlocks₂₂ = c • X.toBlocks₂₂ := rfl
  simp only [tau, h3, h4, cM_smul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_add]

def act (k : ℕ) : Mat p q →ₗ[ℂ] Module.End ℂ (PolB p q) where
  toFun Y := (k : ℂ) • LinearMap.mulLeft ℂ (tau Y) -
    ∑ ij : Fin p × Fin q, LinearMap.mulLeft ℂ (vf Y ij.1 ij.2) ∘ₗ (MvPolynomial.pderiv ij).toLinearMap
  map_add' X Y := by
    refine LinearMap.ext fun P => ?_
    simp [vf_add, tau_add, add_mul, Finset.sum_add_distrib, LinearMap.sum_apply]
    abel
  map_smul' c X := by
    refine LinearMap.ext fun P => ?_
    simp [vf_smul, tau_smul, LinearMap.sum_apply, smul_sub, Finset.smul_sum, smul_comm c (k : ℂ)]

theorem Jm_eq : Jm p q = Matrix.fromBlocks 1 0 0 (-1) := rfl

theorem InU.blocks {x : Mat p q} (h : InU x) :
    x.toBlocks₁₁ᴴ * x.toBlocks₁₁ = 1 + x.toBlocks₂₁ᴴ * x.toBlocks₂₁ ∧
    x.toBlocks₁₁ᴴ * x.toBlocks₁₂ = x.toBlocks₂₁ᴴ * x.toBlocks₂₂ ∧
    x.toBlocks₂₂ᴴ * x.toBlocks₂₂ = 1 + x.toBlocks₁₂ᴴ * x.toBlocks₁₂ := by
  unfold InU at h
  rw [← Matrix.fromBlocks_toBlocks x, Jm_eq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul] at h
  obtain ⟨h1, h2, -, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; abel
  · rw [← sub_eq_zero, ← h2]; abel
  · rw [← sub_eq_zero, ← neg_eq_zero, ← sub_eq_zero.2 h4]; abel

theorem InU.mul {x y : Mat p q} (hx : InU x) (hy : InU y) : InU (x * y) := by
  unfold InU at *
  rw [Matrix.conjTranspose_mul]
  calc _ = yᴴ * (xᴴ * Jm p q * x) * y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hx, hy]

theorem toBlocks₁₂_mul (g x : Mat p q) :
    (g * x).toBlocks₁₂ = g.toBlocks₁₁ * x.toBlocks₁₂ + g.toBlocks₁₂ * x.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g, ← Matrix.fromBlocks_toBlocks x, Matrix.fromBlocks_multiply]
  rfl

theorem toBlocks₂₂_mul (g x : Mat p q) :
    (g * x).toBlocks₂₂ = g.toBlocks₂₁ * x.toBlocks₁₂ + g.toBlocks₂₂ * x.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g, ← Matrix.fromBlocks_toBlocks x, Matrix.fromBlocks_multiply]
  rfl

theorem col₁₂ (Z : Fin p × Fin q → ℂ) : (col Z).toBlocks₁₂ = Matrix.of fun i j => Z (i, j) := rfl

theorem col₂₂ (Z : Fin p × Fin q → ℂ) : (col Z).toBlocks₂₂ = 1 := rfl

def cm (T : GrpData p q) (g : T.G) : Mat p q := ((T.cov g : GL (Ix p q) ℂ) : Mat p q)

instance t2Space_cuspAdeles (T : GrpData p q) : T2Space T.G := T.emb.t2Space

instance instSecondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact T.emb.secondCountableTopology

instance instLocallyCompact (T : GrpData p q) : LocallyCompactSpace T.G := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  exact (GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).locallyCompactSpace

end GlobalTheory.HolDS

end
