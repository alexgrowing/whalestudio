import Mathlib
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.KernelSt
import Development.AbelianVarietyTheory.BlockTheory.ClassSums.StabilizerKernelSums
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RowsCongrOfTrivialAtLevel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.IndefiniteRowSideFullHecke.StabilizerKernelSums
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.KernelCompare

variable {D : D7} {S T : HSp D}

theorem isTh_uVec (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) {f : WO S T → ℂ} (hf : C.IsTh f) :
    C.IsTh (C.uVec Lv hn f) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  exact finsum_induction C.IsTh h0 (fun x y hx hy => (h1 x y hx hy).1)
    fun c => (h2 _ ((h2 f hf).2.1 _)).1 _

def CoefIntegrable : Prop := InWeilActionSetting fun _ om _ μ 𝓕 _ u => MatrixCoefficientIntegrability om μ 𝓕 u

def CoefMass : Prop := InWeilActionSetting fun C om Lv μ 𝓕 _ u => MassOff om μ 𝓕 u (C.under Lv) C.X.Λ

def WeightOff : Prop :=
  InWeilActionSetting fun {D _ T} C om Lv μ 𝓕 _ u => ∃ (θ₀ : ℝ) (b : Lt D.host.E T.rank → ℝ), θ₀ < 1 ∧ (∀ L, 0 ≤ b L) ∧
    Summable (fun L : {L // L ≠ C.X.Λ} => b L.1) ∧ ∑' L : {L // L ≠ C.X.Λ}, b L.1 ≤ θ₀ ∧
    ∀ g ∈ offGrp T (C.under Lv), ∀ L : Lt D.host.E T.rank, L.FG → IsMov (fmt T g) C.X.Λ L →
      ‖coef om μ 𝓕 u g‖ ≤ b L * ‖coef om μ 𝓕 u 1‖

def CoefLowerMass : Prop :=
  InWeilActionSetting fun {_ _ T} C om Lv μ 𝓕 _ u => coef om μ 𝓕 u 1 ≠ 0 → ∀ ν : Measure (offGrp T (C.under Lv)),
    ν.IsHaarMeasure → ν (offStab T (C.under Lv) C.X.Λ) = 1 →
      ∫⁻ g in (offStab T (C.under Lv) C.X.Λ)ᶜ, ‖‖coef om μ 𝓕 u g / coef om μ 𝓕 u 1‖‖ₑ ∂ν < 1

def CoefCont : Prop :=
  InWeilActionSetting fun {_ _ T} C om Lv μ 𝓕 _ u => Continuous fun g : offGrp T (C.under Lv) => ‖coef om μ 𝓕 u g‖

def LevelEigen : Prop :=
  ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ k ∈ GfC S, CongK S (stdL D.host.E S.rank) M k → ∀ (k' : GA D T) (κ : Lv.J), C.LevK Lv k' κ → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, k') (C.uVec Lv hn f') = c • C.uVec Lv hn f'

def CoefInv : Prop :=
  InWeilActionSetting fun {_ _ T} C om Lv μ 𝓕 _ u => ∀ g : offGrp T (C.under Lv), ∀ k ∈ offStab T (C.under Lv) C.X.Λ,
    ‖coef om μ 𝓕 u (g * k : offGrp T (C.under Lv))‖ = ‖coef om μ 𝓕 u g‖

end GlobalTheory.Ker.KernelCompare
