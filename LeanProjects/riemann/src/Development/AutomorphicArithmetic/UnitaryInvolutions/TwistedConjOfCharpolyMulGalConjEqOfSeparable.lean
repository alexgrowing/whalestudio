import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ModelEx
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ReflectCpInv
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.TBase
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.TClass
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ThInvVal
open Matrix Polynomial
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem twistedInverse_mul (c : R ≃ₐ[k] R) (a b : GL (Fin n) R) :
    th c (a * b) = th c a * th c b := by
  refine Units.ext ?_
  change ct c ((a * b)⁻¹ : GL (Fin n) R).val =
    ct c (a⁻¹ : GL (Fin n) R).val * ct c (b⁻¹ : GL (Fin n) R).val
  rw [_root_.mul_inv_rev, Units.val_mul, ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

private theorem twistedInverse_one (c : R ≃ₐ[k] R) : th c (1 : GL (Fin n) R) = 1 := by
  refine Units.ext ?_
  change ct c ((1 : GL (Fin n) R)⁻¹ : GL (Fin n) R).val = 1
  rw [inv_one, Units.val_one, ct, Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]

private theorem twistedConj_mul (c : R ≃ₐ[k] R) (u v d : GL (Fin n) R) :
    thConj c (u * v) d = thConj c v (thConj c u d) := by
  simp only [thConj, twistedInverse_mul, _root_.mul_inv_rev, mul_assoc]

private theorem twistedConj_one (c : R ≃ₐ[k] R) (d : GL (Fin n) R) : thConj c 1 d = d := by
  simp only [thConj, twistedInverse_one, inv_one, one_mul, mul_one]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.twistedConj_of_charpoly_mul_galConj_eq_of_separable :
    ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R), UpperTheory.ConvolutionTheory.D.IsGal c 2 →
        (∀ (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (_ : Module.Basis (Fin n) k A) (x : Aˣ), UpperTheory.ConvolutionTheory.D.NormIn c x) →
        ∀ (n : ℕ) (d d' : GL (Fin n) R), (UpperTheory.ConvolutionTheory.D.cp (d * UpperTheory.ConvolutionTheory.D.th c d)).Separable →
          UpperTheory.ConvolutionTheory.D.cp (d' * UpperTheory.ConvolutionTheory.D.th c d') = UpperTheory.ConvolutionTheory.D.cp (d * UpperTheory.ConvolutionTheory.D.th c d) →
          ∃ t, d' = UpperTheory.ConvolutionTheory.D.thConj c t d := by
  intro k R _ _ _ _ c hG hN n d d' hsep hcp
  haveI : Nontrivial R := hG.inj.nontrivial
  have hP := (UpperTheory.ConvolutionTheory.D.csrOf k R c hG.pow n).2 d
  obtain ⟨A, _, _, b, g, hg, hgP⟩ := UpperTheory.ConvolutionTheory.D.modelEx k R c hG n _ hP hsep
  obtain ⟨w, hw⟩ := UpperTheory.ConvolutionTheory.D.tBase k R A n b c hG g hg
  obtain ⟨x, y, hx⟩ := UpperTheory.ConvolutionTheory.D.tClass k R A n b c hG g hg w hw d hgP.symm
  obtain ⟨x', y', hx'⟩ := UpperTheory.ConvolutionTheory.D.tClass k R A n b c hG g hg w hw d' (hcp.trans hgP.symm)
  obtain ⟨z, hz⟩ := hN A n b (x' / x)
  have h2 := (((UpperTheory.ConvolutionTheory.D.tIso k R A n b c hG g hg w hw).2 x x' _ _ hx hx').2
    (UpperTheory.ConvolutionTheory.D.matU b z)).2 ⟨z, rfl, hz⟩
  refine ⟨y * UpperTheory.ConvolutionTheory.D.matU b z * y'⁻¹, ?_⟩
  rw [UpperTheory.ConvolutionTheory.D.twistedConj_mul, UpperTheory.ConvolutionTheory.D.twistedConj_mul c y, ← h2,
    ← UpperTheory.ConvolutionTheory.D.twistedConj_mul, mul_inv_cancel, UpperTheory.ConvolutionTheory.D.twistedConj_one]
