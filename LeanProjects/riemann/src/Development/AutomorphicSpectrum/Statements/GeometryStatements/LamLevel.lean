import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TraceWedgePairingPerfectRationalForms
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AbsAZero
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.MeanLogS

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LamLevel : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (V : HSp D)
    (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r), LevelLaws U V dict →
    ∀ (large₂ : SizeData₂ D) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ S L : ℝ, SizeRows D l.M S L →
    (absA Dw a : ℝ) + D.R.f * D.R.r * n ≤ S →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) c.F (cusp Xo c U a n)),
      letI : StarRing c.F := starRingOfComm
      Formalism.NormVectorIdentities.Items.LamS (latCoord U a n b)
        (fun v => Formalism.L2.DIV.frameOf
          (gramAt U V dict (lieFac Dw (xiR D) a) (fun i => (b i : Rul Xo c)) v.embedding))
        (lamConst C D.R.f D.R.r L (dE D.host.E) large₂.logOm S)

end GlobalTheory.CompanionTheory.Ar.abelian₂
