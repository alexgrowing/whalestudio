import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Member.DomFin

theorem exists_dominating_fintype : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M₀ : GlobalTheory.TrueGeo.Model Y)
    (ι : Type) [Fintype ι] (M : ι → GlobalTheory.TrueGeo.Model Y), ∃ (P : GlobalTheory.TrueGeo.Model Y) (π : ∀ i, P.X ⟶ (M i).X),
      ∀ i, π i ≫ (M i).p = P.p ∧ P.j ≫ π i = (M i).j := by
  intro F _ _ Y M₀ ι _ M
  classical
  obtain ⟨P, -, -, -, hdom⟩ := GlobalTheory.LineNorm.Glue.exists_normal_dominating_finset M₀ M Finset.univ
  choose ρ hρ using fun i => hdom i (Finset.mem_univ i)
  refine ⟨P, ρ, fun i => ⟨?_, hρ i⟩⟩
  have := P.ar.isIntegral
  have : IsDominant P.j := ⟨(dense_iff_closure_eq.2 (genericPoint_spec P.X)).mono
    (Set.singleton_subset_iff.2 ⟨_, ((GlobalTheory.TrueGeo.SmallSec.j_gen_specializes P).antisymm
      (genericPoint_specializes _)).eq⟩)⟩
  refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) P.j ?_
  rw [← Category.assoc, hρ i, (M i).pb.w, P.pb.w]

end GlobalTheory.Member.DomFin
