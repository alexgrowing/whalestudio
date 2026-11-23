import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemAmpleFramesFullLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RaisedModelFiniteCoverAmpleFramesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClausesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelStructureConditionsAndSplitFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

theorem exists_localSystems_ample :
    GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  intro hext hL hL2 hL3 htop hN1 E _ _ _ H D hpq Xo
  obtain ⟨-, hN⟩ := hN1
  have hlev : ToroidalLevelCompatibility (H := H) (D := D) := (hN E H D hpq).1

  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel hext hL hL2 hL3 htop E H D Xo hpq hlev
  refine ⟨S.Y, fun p W hp hW => ⟨GlobalTheory.T.localModelSystem_transition_siegel_clauses hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW, fun i => ?_⟩,
    GlobalTheory.T.exists_global_model_of_local_models hext hL hL2 hL3 E H D Xo hpq hlev S⟩
  refine ⟨(GlobalTheory.T.localModel_oneModel_and_splitFibres hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW i).2, ?_⟩

  obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
  obtain ⟨k, hk⟩ := hS (S.ch p)
  have hc := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
  have hcop : (S.n (S.ch p)).Coprime p := (Nat.coprime_primes (S.aux _).1 hp).2 (S.ch_ne p)
  exact GlobalTheory.T.raised_model_finite_cover_ample_frames hL hL2 hL3 E H D Xo (S.n (S.ch p)) (S.n (S.ch p) ^ S.J (S.ch p)) k (S.T (S.ch p)) hlev
    l₀ i.l (S.B (S.ch p) l₀ h₀.1) i.c _ (i.c.V W).subtype (S.Y p W hp hW i) (S.aux _).1 (S.aux _).2.1
    ⟨_, rfl⟩ (hc.2.1 _ hcop) ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 i.l l₀ h₀).1 hc.1 hr hk

end GlobalTheory.Models
