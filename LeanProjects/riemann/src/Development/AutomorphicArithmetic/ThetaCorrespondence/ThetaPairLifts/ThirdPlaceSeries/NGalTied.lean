import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DaAutRepSphAt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain
namespace Formalism.L2
structure AUTiedAlt (D : D7) (L : LPTiedPlaceholder D) (M : MtFam D) (A : AVTied D M) where
  cls : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AutRep D.host.E D.R.nV → D.nbc.AU j
  surj : ∀ j h1 h2, Function.Surjective (cls j h1 h2)
  iso : ∀ j h1 h2 π π', cls j h1 h2 π = cls j h1 h2 π' ↔ π.Iso π'
  mult : ∀ j h1 h2 π, D.nbc.multAU j (cls j h1 h2 π) = π.mult
  sph : ∀ j h1 h2 π (w : PlE D.host) v, ¬ IsSplitPl D.host w → NG.OverPl w v →
    (D.nbc.sphAU j (cls j h1 h2 π) w ↔ π.SphericalAtPlace v)
  sat : ∀ j h1 h2 π v (w : PlE D.host), NG.OverPl w v → ∀ (Dv : InertDatum D.host.E D.R.nV v w), (∃ α, NG.SatAt π Dv α) →
    ∃ α, NG.SatAt π Dv α ∧ D.nbc.satAU j (cls j h1 h2 π) w = Finset.univ.val.map α
  clsWt : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AlgWt D.host.E D.R.nV → D.nbc.Wt j
  surjWt : ∀ j h1 h2, Function.Surjective (clsWt j h1 h2)
  isoWt : ∀ j h1 h2 a b, clsWt j h1 h2 a = clsWt j h1 h2 b ↔ a.Iso b
  wt : ∀ j h1 h2 π a, π.toAlgWt.IsDual a → D.nbc.wtAU j (cls j h1 h2 π) = clsWt j h1 h2 a
  infW : ∀ j h1 h2 a (τ : D.host.E →+* ℂ) lam, a.HWAt τ lam → D.nbc.infW j (clsWt j h1 h2 a) τ = NG.infOf lam
  emb : ∀ i P, D.nbc.embAV i P = cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (A.rep i P)
structure NGalTiedAlt (D : D7) where
  fr : OmFrame D
  lp : LPTiedPlaceholder D
  mt : MtFam D
  hecke : HeckeTied D mt
  av : AVTied D mt
  au : _root_.Formalism.L2.AUTiedAlt D lp mt av
  rational : HeckeRational D mt
  tup : D.what₂.Tup → Fin D.R.m → Host.HChar D.host.E
  level : LevelTied D mt tup
end Formalism.L2
end
end
