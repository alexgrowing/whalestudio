import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW
def Uniq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure →
  ∀ Λ : d.Fn →ₗ[ℂ] ℂ, Λ ∈ (adeleClass F).adm d.κ →
    (∀ Z : Mx F E d.m d.n, ∀ Φ ∈ d.sch, Λ (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) = Λ Φ) →
    ∃ C : ℂ, ∀ Φ ∈ d.sch, Λ Φ = C * ∫ Z, d.T Φ Z ∂ν
def UpTo_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure → ∀ ε w, d.IsW ε w → ∃ C : ℂ, ∀ Φ ∈ d.sch,
  ∀ X, d.T (d.om w Φ) X = C * ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.T Φ Z ∂ν
def Poisson_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν, d.IsCov ν → ∀ ε : ℤˣ, ∀ f ∈ d.schM,
  ∑' X : Matrix (Fin d.m) (Fin d.n) E, ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F X) Z)) * f Z ∂ν =
    ∑' X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X)
def ThetaW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, d.om w Φ ∈ d.sch ∧ thetaSum F (d.om w Φ) = thetaSum F Φ) ∧
  ∃ Φ ∈ d.sch, thetaSum F Φ ≠ 0
theorem tWeyl_of_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (h1 : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k) : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ X
  obtain ⟨C, hC⟩ := h1 F E σ d ν hν.1 ε w hw
  obtain ⟨hθ, Φ₀, h0, hne⟩ := h3 F E σ d
  have e1 := (hT F E σ d _ (hθ ε w hw Φ₀ h0).1).1.tsum_eq
  have e2 := (hT F E σ d _ h0).1.tsum_eq
  have e3 := h2 F E σ d ν hν ε _ ((hB F E σ d).1 Φ₀ h0)
  simp only [hC Φ₀ h0] at e1
  rw [tsum_mul_left, e3, e2, (hθ ε w hw Φ₀ h0).2] at e1
  have : C = 1 := mul_right_cancel₀ hne (e1.trans (one_mul _).symm)
  rw [hC Φ hΦ X, this, one_mul]
end PositivityTheory.SiegelWeilFormula.TW
end
end
