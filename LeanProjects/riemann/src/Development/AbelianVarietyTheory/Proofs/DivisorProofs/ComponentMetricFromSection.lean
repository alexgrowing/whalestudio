import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSncPullbackSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundaryPotentialSncStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory

theorem fromSec_of_core : ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H → ∀ c, (T.M c).FromSec := by
  rintro D O ⟨x, P, h⟩ A T H R c a
  have := GlobalTheory.T.complex_points_connected _ (O.var c) ((R.man c).ε a)
  refine ⟨((R.man c).pt a).symm.surjective.connectedSpace ((R.man c).pt a).symm.continuous, ?_⟩
  have hπ := GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c
  have : Smooth (genStr O.s.T.Z) := SmoothOfRelativeDimension.smooth O.S.Dw.dim _
  have : IsLocallyNoetherian (gen O.s.T.Z : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian (genStr O.s.T.Z)
  have := isProper_genStr O.s.T.Z
  have : CompactSpace (gen O.s.T.Z : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (genStr O.s.T.Z)
  have : IsNoetherian (gen O.s.T.Z : Scheme.{0}) := {}
  obtain ⟨L, t, h₁, h₂⟩ := GlobalTheory.T.exists_boundary_potential_snc _ (O.var c) _ (T.M c) (R.man c) a x.m (fun i => (x.cpt i).preimage (O.Φ.C c).π.continuous)
    (fun i z => x.nrm _ i ((O.Φ.C c).down z)) (O.dim_eq c)
    (fun y => GlobalTheory.T.local_snc_pullback_smooth _ _ _ (genStr O.s.T.Z) _ _ _ y (GlobalTheory.T.snc_components_local_snc _ _ _ _ O.s.T.snc x.cpt_list _))
    (fun i => GlobalTheory.T.divisor_norm_pullback_component D _ _ _ _ _ O.s O.Φ c _ _ _ hπ (x.nrm_div _ i))
    (fun z => ((R.an c).Z a z).trans (x.liesIn_genBd_iff ((O.Φ.C c).down ((R.man c).pt a z))))
    (fun z hz => ((R.an c).r a z hz).trans (by rw [h.r_eq]; rfl))
  exact ⟨L, t, h₁, _, _, h₂⟩

end GlobalTheory
