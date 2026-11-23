import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EisensteinSeriesContinuationModuli
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.RgEis

def ContSplit : Prop :=
  ∀ (D : D7) (T : HSp D) (r : ℕ) (d : HypDec T (zeroSp D) r) (L : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (a : GL (Fin T.rank) (AE D)), IsLevel T L a → HasIw d (lev T L a) → ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ),
    IsHeckeChar D μ → ResEta D μ b → ∀ (t s₁ : ℂ), ∀ φ ∈ indSpace (absDet d) (lev T L a) (detChar d μ) t,
      ContMod T fun s g => GlobalTheory.Eis.cosetSum (GlobalTheory.RegSW.stab d) (GQ T) (flatSec (absDet d) (lev T L a) φ s₁ s) g

def SphericalEisensteinContinuation : Prop :=
  ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), IsAniso T₀ → ∀ b : GL (Fin T.rank) (AE D), IsMaj T b →
    HasIw d (Kmax T b) → (∀ h, Continues (sphericalEisenstein d b h)) ∧ ∀ s₀, ∃ k, EisensteinRegularAt d b s₀ k

end PositivityTheory.RgEis
