import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocFinE
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.EulerS
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelDensitiesOfHermitianForm
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont
open scoped TensorProduct

namespace PositivityTheory.PfSWUS.HMass

open GlobalTheory.CompanionTheory.SW Topology
open scoped ENNReal NNReal Matrix

def SWMeasEdge : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J →
  ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeas σ J T hT

def SchwartzDensInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n))
    (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m →
    ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, PositivityTheory.PfSWUS.Loc.IsSchwartzInf φ →
      Continuous φ ∧
      IsContDensityOn μ (gramR (Ainf F) σ J) Subtype.val ν
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} φ (fun S => ∫ X, φ X ∂(m S)) ∧
      ∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)

theorem isUnit_det_hermOf {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hd : T.det ≠ 0) :
    IsUnit ((hermOf R σ T hT : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
  change IsUnit ((inclR (F := F) R).mapMatrix T).det
  rw [← RingHom.map_det]
  exact (isUnit_iff_ne_zero.2 hd).map _

end PositivityTheory.PfSWUS.HMass
