import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem sum_coord_re {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (z : Cinf E) :
    ∑ τ : E →+* ℂ, coord τ z = ((2 * ∑ w : InfinitePlace E, (z w).re : ℝ) : ℂ) := by
  have h := congrArg Multiplicative.toAdd
    (GlobalTheory.GKCoh.Tests.prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd z)
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd, Complex.add_conj] at h
  rw [h, Finset.mul_sum, Complex.ofReal_sum]

theorem UpperTheory.V.Lit.Bor.twEx :
    UpperTheory.V.Lit.Bor.TwEx := by
  intro E _ _ _ a _ r
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (r / (2 * ((a : ℝ) * Fintype.card (InfinitePlace E))))
  refine ⟨_, ⟨_, hν⟩, fun X φ => ?_⟩
  rw [lie_mulChi, GlobalTheory.CuspRep.AlgExpo.dchi_eq_sum]
  simp only [(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 _ hν, ← Finset.mul_sum]
  rw [sum_coord_re, ← Complex.ofReal_mul]
  have e : ell E a X = (∑ w : InfinitePlace E, ((Matrix.of X).trace w).re) /
      ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp [ell, Matrix.trace]
  rw [e]
  congr 4
  ring
