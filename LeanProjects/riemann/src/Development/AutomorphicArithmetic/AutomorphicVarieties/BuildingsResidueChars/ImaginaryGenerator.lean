import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.imaginary_generator :
    UpperTheory.V.Af.Cr.ImagGen := by
  intro K _ _ _ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  obtain ⟨d, e, -, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq ℚ K
  have hy : e 1 ^ 2 = (d : K) := by rw [sq, h1]; simp
  have hx : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * e 1 := fun x => by
    refine ⟨e.repr x 0, e.repr x 1, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, Rat.smul_def, Rat.smul_def, mul_one]
  refine ⟨d, e 1, ?_, hy, hx⟩
  by_contra hd
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast not_lt.1 hd
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  have hφ : φ (e 1) ^ 2 = ((Real.sqrt d : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hy, ← Complex.ofReal_pow, Real.sq_sqrt hd0]
    simp
  have hc : (starRingEnd ℂ) (φ (e 1)) = φ (e 1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hφ with h2 | h2 <;> simp [h2]
  rw [ComplexEmbedding.isReal_iff]
  ext1 x
  obtain ⟨a, b, rfl⟩ := hx x
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp [hc]
