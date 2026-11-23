import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cmData_sig_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : ∃ a, hc.sig a ≠ a := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (h a)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩).finrank_eq.symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

theorem exists_isDetRoot : ∀ (D : D7) (V : HSp D) (g : GA D V), ∃ x, IsDetRoot V g x := by
  intro D V g
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig
      (AlgHom.ext fun a => star_star a) (AlgHom.ext fun a => star_star a)
  have hc1 : c ≠ 1 := by
    obtain ⟨a, ha⟩ := cmData_sig_ne_id D.sp.cm
    intro h
    exact ha (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)
  have hu := det_conj_mul V g
  rw [mul_comm] at hu
  exact GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic D.host.F D.host.E c D.sp.cm.deg2 hc1 (Formalism.L2.Theta.mt V g).det hu

end GlobalTheory.RecDict
