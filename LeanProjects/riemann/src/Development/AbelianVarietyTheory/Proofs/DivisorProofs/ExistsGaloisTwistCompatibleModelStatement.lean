import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTwistCompatibleModel
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open CategoryTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_twist_compatible_model : Hypotheses2 → ∀ (D : D7) (O : Setup D), O.Core → ∀ h ∈ D.R.Psi,
    ∃ (σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E) (r : (O.S.Xo O.κ.l).XF O.κ.c ≅ (O.S.Xo O.κ.l).XF O.κ.c),
      (∀ a : 𝓞 D.host.E, ((σ a : 𝓞 D.host.E) : D.host.E) = D.host.sigmaOf h (a : D.host.E)) ∧
      σ O.A.H.w0 = O.A.H.w0 ∧ Nonempty (GlobalTheory.ShFam.TwMap σ O.s.T.Z.oF.t O.s.T.Z.oF.t r.hom) ∧
      r.hom ≫ CategoryTheory.Limits.pullback.snd _ _ = CategoryTheory.Limits.pullback.snd _ _ := by
  first | exact @GlobalTheory.GalTwist.twist_aut | exact GlobalTheory.GalTwist.twist_aut | (intros; apply GlobalTheory.GalTwist.twist_aut <;> assumption)
