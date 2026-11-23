import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.SphericalEisensteinContinuation
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf

noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine PositivityTheory.RgEis ResidueKilled.Tr
open GlobalTheory.Core.Rk.SWLaw (zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.RgEis.Sp

def ChartSplit : Prop :=
  ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (T : HSp D) (r : ℕ) (d : HypDec T (zeroSp D) r)
    (L : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : GL (Fin T.rank) (AE D)),
    IsAdapted D.sp.cm.sig T.gram d.e d.e' L a → ∃ (ε : ℤˣ) (Φ : GA D T ≃ₜ* (adCM D.sp.cm.sig χ).U ε (Fin r)) (p : GlobalTheory.RegSW.stab d),
    (∀ g, g ∈ GQ T ↔ Φ g ∈ (adCM D.sp.cm.sig χ).uΓ ε (Fin r)) ∧
    (∀ g, g ∈ GlobalTheory.RegSW.stab d ↔ Φ g ∈ (adCM D.sp.cm.sig χ).uQ ε (Set.univ : Set (Fin r))) ∧
    (∀ k, k ∈ lev T L a ↔ Φ ((p : GA D T)⁻¹ * k * p) ∈ (adCM D.sp.cm.sig χ).uK ε (Fin r)) ∧
    (∀ q : GlobalTheory.RegSW.stab d, bdet (Sum.inl '' (Set.univ : Set (Fin r))) (Φ q).1 = Matrix.GeneralLinearGroup.det (GlobalTheory.RegSW.onX d q)) ∧
    ∀ x : (AE D)ˣ, (adCM D.sp.cm.sig χ).lg x = Real.log (absA D x)

def ContAd : Prop :=
  ∀ (D : D7) (T : HSp D) (r : ℕ) (d : HypDec T (zeroSp D) r) (L : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (a : GL (Fin T.rank) (AE D)), IsAdapted D.sp.cm.sig T.gram d.e d.e' L a → IsIwasawa (absDet d) (lev T L a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b → ∀ (t s₁ : ℂ),
    ∀ φ ∈ indSpace (absDet d) (lev T L a) (detChar d μ) t,
      ContMod T fun s g => GlobalTheory.Eis.cosetSum (GlobalTheory.RegSW.stab d) (GQ T) (flatSec (absDet d) (lev T L a) φ s₁ s) g

def TContAd : Prop := CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll → ChartSplit → Scal → Div → ContAd

def TContSplit : Prop := ContAd → ContSplit

def TChartSplit : Prop := Dict → DictInf → ChartSplit

end PositivityTheory.RgEis.Sp
