import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing

open MeasureTheory Set Filter NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.RegularCuspidalTrace

def IsCuspFn {D : D7} {V : HSp D} (f : GA D V → ℂ) : Prop :=
  ∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f

def RegClassInt : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (f : GA D V → ℂ), f ∈ CcGA V → IsCuspFn f →
    ∀ γ : GF V, IsRegSS γ.1.1 →
      Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ)

def RegClassFin : Prop :=
  ∀ (D : D7) (V : HSp D) (f : GA D V → ℂ), f ∈ CcGA V →
    {𝔬 : Set (GF V) | (∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}) ∧
      ∃ (x : GA D V) (δ : GF V), δ ∈ 𝔬 ∧ f (x⁻¹ * rat V δ * x) ≠ 0}.Finite

def RegClassWO : Prop :=
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure], ∀ f ∈ CcGA V, IsCuspFn f → ∀ γ : GF V, IsRegSS γ.1.1 →
      ∀ P, IsMinLevi Φ γ P → P ≠ ∅ →
      ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], ∃ c : ℝ, ∀ T, Regular c T →
        ∫ q, descend (GQ V) (kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ δ} f T) q ∂autMeasure V μ =
          volA Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) (cent (rat V γ)) dt *
            wOrbInt (cent (rat V γ)) dt μ (rat V γ)
              (fun x => weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) T x) f

end MainStatements.RegularCuspidalTrace

end
