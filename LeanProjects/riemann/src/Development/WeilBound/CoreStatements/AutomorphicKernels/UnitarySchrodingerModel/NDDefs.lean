import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

noncomputable section

section LocS

namespace PositivityTheory.PfSWUS.Loc

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trPair (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (∑ a, ∑ c, S a c * T c a)

def jtR (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ Y, φ Y * ψR (trPair R (b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (gramR R σ J Y)) ∂μ

def latO {d n : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fin n → Fv F v ⊗[F] E) :=
  {y | ∀ a k, (Algebra.TensorProduct.basis (Fv F v) bs).repr (y a) k ∈ v.adicCompletionIntegers F}

def nuV {d n : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fin n → Fv F v ⊗[F] E))
    (σ : E →ₐ[F] E) (b : HermR (Fv F v) σ n) : ℝ :=
  (lam {x | ∃ y ∈ latO bs v, ∃ y' ∈ latO bs v,
      x = y + (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).mulVec y'} / lam (latO bs v)).toReal

def hInf (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (Ainf F) σ n) : ℝ :=
  ∏ τ : InfinitePlace F, ‖Algebra.norm (Ainf F)
    ((1 + (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det) τ‖

def IsSchwartzInf {n M : ℕ} (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∀ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
    ∃ f : SchwartzMap (Fin N → ℝ) ℂ, ∀ x, f x = Φinf (e.symm x)

def LocFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n < M →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ), HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F ψ →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)),
    SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
  ∀ (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
  ∀ g : HermR (Fv F v) σ n → ℂ,
    IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv g →
  ∀ T : HermR (Fv F v) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det →
    HolValueAt (fun z => ∫ b, ((nuV bs v lam σ b : ℝ) : ℂ) ^ (-(z - ((M : ℂ) - n) / 2)) *
        jtR (Fv F v) σ J (psiV F ψ v) μv Φv b *
        psiV F ψ v (-trPair (Fv F v) (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) b) ∂νv)
      (((M : ℂ) - n) / 2) (g T)

def SiegelDensitiesLow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (n : ℕ), n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    IsSchwartzInf Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

end PositivityTheory.PfSWUS.Loc

end LocS

section D7S

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

def WhitNDg : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n), CoefData nb lam 𝓖 →
  ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g : G D n,
    HolValueAt (fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ (ω g Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
      (s0 V n) (IfrB V ν (ω g Φ).1 β)

def NDOfWhit : Prop := Unfold → ThetaCoef → WhitNDg → CoefND

end PositivityTheory.PfSWUS

namespace PositivityTheory.PfSWUS

def WhitNDgOfLocal : Prop := Loc.LocFin → PositivityTheory.Rg.Sw.WR.WRSt → Loc.SiegelDensitiesLow → WhitNDg

end PositivityTheory.PfSWUS

end D7S

end
