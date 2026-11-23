import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd

theorem psiFin_add' (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := by
    simp only [pairA]
    exact Prod.ext (add_zero 0).symm rfl
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem hR_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add, Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem hR_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add, Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem pairB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  intro F E _ _ _ _ _ σ M J n ψ b
  have hg1 : ∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J (X + X') Y = gram2 σ J X Y + gram2 σ J X' Y := by
    intro X X' Y
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_left _ σ J _ _ _
  have hg2 : ∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J X (Y + Y') = gram2 σ J X Y + gram2 σ J X Y' := by
    intro X Y Y'
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_right _ σ J _ _ _
  refine ⟨fun X X' Y => ?_, fun X Y Y' => ?_⟩
  · simp only [pairB, hg1, Matrix.mul_add, Matrix.trace_add, map_add, psiFin_add']
  · simp only [pairB, hg2, Matrix.mul_add, Matrix.trace_add, map_add, psiFin_add']

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd
