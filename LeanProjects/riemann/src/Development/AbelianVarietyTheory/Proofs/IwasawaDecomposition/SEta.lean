import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenThetaMatchStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaEventuallyAgreesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarClosedIntegralLatticeAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebotarevSplitAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAllStatement

noncomputable section

namespace GlobalTheory.StEta

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem sEta : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PtSt hL → SEta hL := by
  intro hP hL hPt
  refine ((((((hPt.and (GlobalTheory.T.eta_eventually_agrees hP hL hPt)).and (GlobalTheory.T.star_closed_integral_lattice_all hP hL)).and (GlobalTheory.T.exponent_integral_all hP hL)).and (GlobalTheory.T.auxiliary_places_split_all hP hL)).and (GlobalTheory.T.chebotarev_split_all hP hL)).and
    (GlobalTheory.T.galois_reps_cuspidal_all hP hL)).trans (StepW.of_all ?_)
  intro K B f T w _ _ H P x l hB
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hst⟩, hex⟩, hsp⟩, hch⟩, h4⟩ := H
  have law := fun P₁ P₂ => GlobalTheory.CoefDuty.LargeRing.evO_laws (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have hin : GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      (SumRepresentations.hypO D' → SumRepresentations.Conclusion41 D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D' :=
    (law _ _).1 ((law _ _).2.1 (fun D' h hO => ⟨(h.1 hO).1, (h.1 hO).2.1⟩) (h1 P x l)) (h4 P x l)
  have hMt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
    rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
  have hm := (GlobalTheory.T.side_eigen_theta_match hP.cheb (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig
    l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hMt (hst P x l) (hex P x l) (hsp P x l) (hch P x l) hB hin).1
  refine (law _ _).2.1 ?_ ((law _ _).1 hm (h2 P x l))
  intro D' h
  have hO : SumRepresentations.hypO D' := by have h' := h.1.1; unfold GlobalTheory.CoefDuty.Large at h'; exact h'.1
  exact ⟨h.1.1, h.2 hO⟩

end GlobalTheory.StEta

end
