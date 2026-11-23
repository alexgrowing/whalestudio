import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

variable {D : D7}

abbrev Loc (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

def atV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : Loc V v) : GA D V := emb D.sp.cm.sig V.gram v h

variable {n : ℕ} {V V₀ : HSp D} {r : ℕ} {K : Subgroup (GA D V)} (ν : Measure K) {v : HeightOneSpectrum (𝓞 D.host.F)}

def heckeS (z : Loc V v →₀ ℂ) (Φ : Mx D V.rank n → ℂ) : Mx D V.rank n → ℂ :=
  z.sum fun h c => c • projS ν fun x => Φ (mt V (atV V v h)⁻¹ ⬝ x)

def heckeF (z : Loc V v →₀ ℂ) (f : GA D V → ℂ) : GA D V → ℂ :=
  fun x => z.sum fun h c => c * ∫ k, f (x * (k : GA D V) * (atV V v h)⁻¹) ∂ν

variable {θ : InfFam D} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)) (d : HypDec V V₀ r) (K)

def regIntH (m : Measure (GA D V)) (P : ℂ → ℂ) (Ψ : schwartzA θ V.rank n) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => (residueFieldAlt d K * P s)⁻¹ *
    ⨍ q, descend (GQ V) (fun h => StdUnn.theta ω Ψ g h * sphericalEisensteinSeriesOnGroup d K h s) q ∂autMeasure V m

variable {K}

def IsRegH (m : Measure (GA D V)) (z : Loc V v →₀ ℂ) (P : ℂ → ℂ) (Φ Ψ : schwartzA θ V.rank n) : Prop :=
  Ψ.1 = heckeS ν z Φ.1 ∧ (∀ s, heckeF ν z (sphericalSectionIwasawa d K s) = P s • sphericalSectionIwasawa d K s) ∧ P ≠ 0 ∧
  (∀ g, Grow.RapidDec V (StdUnn.theta ω Ψ g)) ∧
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ g,
    Integrable (descend (GQ V) fun h => StdUnn.theta ω Ψ g h * sphericalEisensteinSeriesOnGroup d K h s) (autMeasure V m)

end GlobalTheory.RegSch

end
