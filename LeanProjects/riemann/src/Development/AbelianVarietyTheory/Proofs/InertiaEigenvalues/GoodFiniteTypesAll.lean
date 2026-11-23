import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateVectorInSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentationComponentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodMem

set_option maxHeartbeats 4000000 in

theorem goodFTAll_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GoodFTAll (w.D Z) := by
  intro hP hL
  have hA := GlobalTheory.T.coefficient_duty_in_place hL
  have hO := GlobalTheory.T.conjugate_vector_in_subspace hP
  refine EvG.imp (EvG.inter hA hO) fun K _ _ _ _ h => ?_
  refine large₂.imp (large₂.inter h.1 h.2) fun B f T _ g => ?_
  intro hK w Z Wt p0 t nch n xd c _ _ hpin
  have hop := g.1 hK w Z Wt p0 t nch n xd c ‹_› ‹_› hpin
  have hrow := g.2 hK w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt
  refine GlobalTheory.T.exists_representation_component hP.green hP.zel hP.dz hL (w.D Z) _ nch n.tp c.a hop ?_
  have key : ∀ (D' : D7) (_ : D' = withLoc c.a.nt.L) (r' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r), HEq c.a.nt.rep r' →
      (∀ (I : GlobalTheory.TypeRec.Ident D') cp, GlobalTheory.TypeRec.IsComp I r' cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (G0g D'.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D' k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧
        ρ.asAlgebraHom D'.ntypes.e0 x = x) →
      ∀ (I : GlobalTheory.TypeRec.Ident c.a.nt.D) cp, GlobalTheory.TypeRec.IsComp I c.a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V)
        (_ : Module ℂ V) (ρ : Representation ℂ (G0g c.a.nt.D.nd) V) (W : Submodule ℂ V) (x : V),
        (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom c.a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom c.a.nt.D.ntypes.e0 x = x := by
    rintro _ rfl r' hr h
    have e : c.a.nt.rep = r' := eq_of_heq hr
    rw [e]
    intro I cp hc σ
    exact h ⟨I.i, I.cont⟩ cp hc σ
  exact key _ c.a.nt.eq _ c.row.rep_eq hrow

end GlobalTheory.GoodMem
