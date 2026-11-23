import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OverPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongW Formalism.UG GlobalTheory.DefU GlobalTheory.PRep GlobalTheory.CongSc

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

variable [IsCMField E]

theorem cT_cLoc_conjSrc_mul {n : ℕ} (g : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    Matrix.transpose (((cLoc (conjSrc (IsCMField.complexConj E).toRingEquiv u) g : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _).map (conjLoc (IsCMField.complexConj E).toRingEquiv u)) *
      ((cLoc u g : GL (Fin n) (u.adicCompletion E)) : Matrix (Fin n) (Fin n) (u.adicCompletion E)) = 1 := by
  have h : cT (conjAd E) ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) * 1 *
      ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) = 1 := g.2
  rw [Matrix.mul_one] at h
  calc _ = (cT (conjAd E) ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) *
        ((g.1 : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E))).map ((pLoc E u).comp (pFin E)) := by
        rw [Matrix.map_mul]; rfl
    _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

end GlobalTheory.LadicPair

namespace GlobalTheory.LadicPair

end GlobalTheory.LadicPair
