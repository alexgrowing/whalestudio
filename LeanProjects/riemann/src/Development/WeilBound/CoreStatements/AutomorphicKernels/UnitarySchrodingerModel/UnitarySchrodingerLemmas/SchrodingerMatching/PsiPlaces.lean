import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

def aTau (θ : InfFam D) (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) : GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D)) a

def conjH (a : GL (Fin n) (AE D)) (b : hermA D n) : hermA D n :=
  ⟨a.1 * b.1 * adj a.1, by
    have hb : adj b.1 = b.1 := b.2
    change adj (a.1 * b.1 * adj a.1) = a.1 * b.1 * adj a.1
    rw [adj_mul, adj_mul, adj_adj, hb, mul_assoc]⟩

def PsiPlaces : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ →
    HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF D.host.F ψ ∧ PositivityTheory.SiegelWeilFormula.Gen.IsPlaces D.sp.cm.sig ψ θ l

def RealMatch : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → HasRealPar ψ θ l →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
  ∀ (e : D.what₂.Tau × Fin V.rank × Fin n × Bool →₀ ℕ) (c : ℂ) (a : GL (Fin n) (AE D)),
  ∃ (εG : D.what₂.Tau → Fin V.rank → Bool) (frG : D.what₂.Tau → GL (Fin V.rank) ℂ)
    (PG : D.what₂.Tau → PositivityTheory.Rg.Sw.PX V.rank n),
    PositivityTheory.SiegelWeilFormula.Gen.IsFrames (HSpace.gram V) θ εG frG ∧
    ∀ x : Mx D V.rank n,
      evalPoly (MvPolynomial.monomial e c) (fun τ => compAt θ τ (HMul.hMul x a.1)) *
          gauss V l s (fun τ => compAt θ τ (HMul.hMul x a.1)) =
        PositivityTheory.SiegelWeilFormula.Gen.phiInf θ l frG (aTau θ a) PG (HeckeCharacterZeroLocus.SiegelWeilU.projInf (tupInv x))

def RealConj : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (a : GL (Fin n) (AE D)) (b : hermA D n),
    PositivityTheory.SiegelWeilFormula.Gen.nuInf θ (aTau θ a) (PositivityTheory.SiegelWeilFormula.Gen.matInf (conjH a b).1) =
      PositivityTheory.SiegelWeilFormula.Gen.nuInf θ (fun _ => 1) (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1)

def HeightWN : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ θ : InfFam D, IsInfFam θ →
  ∀ nb : hermA D n → G D n, IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
  ∃ L : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
    (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L v)) ∧
    (∀ (d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E),
      ∀ᶠ v in Filter.cofinite, (L v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) =
        PositivityTheory.PfSWUS.Loc.latO bs v) ∧
    ∀ lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
        Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ v, (lam v).IsAddHaarMeasure) →
      ∀ b : hermA D n, ((H (w * nb b) : ℝ))⁻¹ = PositivityTheory.SiegelWeilFormula.Gen.nuA θ (fun _ => 1) lam L L b.1

def FinMatch : Prop :=
  ∀ (D : D7) (n M : ℕ) (a : GL (Fin n) (AE D)) (d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E)
    (g : (Fin M → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (gv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ),
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs (fun X => g fun i j => X j i) gv →
  ∀ (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
        Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (L : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)),
    (∀ v, (lam v).IsAddHaarMeasure) → (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L v)) →
    (∀ᶠ v in Filter.cofinite, (L v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) =
      PositivityTheory.PfSWUS.Loc.latO bs v) →
  ∃ (L₁ L₂ : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E))
    (Φf : (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (Φv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ),
    (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (L₁ v) ∧ PositivityTheory.SiegelWeilFormula.Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in Filter.cofinite,
      (L₁ v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) = PositivityTheory.PfSWUS.Loc.latO bs v ∧
      (L₂ v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) = PositivityTheory.PfSWUS.Loc.latO bs v) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin bs Φf Φv ∧
    (∀ x : Mx D M n, g (fun i j => finPart D ((HMul.hMul x a.1 : Mx D M n) i j)) =
      Φf (HeckeCharacterZeroLocus.SiegelWeilU.projFin (tupInv x))) ∧
    ∀ v (b : hermA D n),
      PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L₁ v) (L₂ v) (PositivityTheory.SiegelWeilFormula.Gen.matV v (conjH a b).1) =
        PositivityTheory.SiegelWeilFormula.Gen.nu2 (lam v) (L v) (L v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1)

def ConjMod : Prop :=
  ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : Mx D n n → ℂ),
    ∫ b, f b.1 ∂lam = ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ n * ∫ c, f (a.1 * c.1 * adj a.1) ∂lam

def MonoSch : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : Mx D V.rank n → ℂ), IsMonoFock θ V l s φ → φ ∈ schwartzA θ V.rank n ∧ φ ∈ fockA θ V n l s

def ValueSide : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ν : Measure (GA D V)), ν.IsHaarMeasure →
  ∀ (φ : Mx D V.rank n → ℂ) (β : HermE D n), β.1.det ≠ 0 →
  ∀ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) μH →
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) μH 𝓕 →
    IfrB V ν φ β = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
      (HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) (fun X => φ (tupOf X))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig (HSpace.gram V) X = β.1})

end PositivityTheory.PfSWUS.SwMatch

end
