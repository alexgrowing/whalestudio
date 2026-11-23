import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.FockOff

theorem latO_le {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {p q : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

end GlobalTheory.EvenOnto.FockOff

open GlobalTheory.EvenOnto.FockOff in

theorem GlobalTheory.EvenOnto.fock_sph_vac : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D c hc k hk s s' hs hs' p hp φ
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hv := hp.pre.vac
  have hF : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) :=
    GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ
  have hpt : ∀ φ', IsThetaFunO c.ψ s.V s'.V (p.pt φ') := fun φ' =>
    (GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ').1
  have hle : latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S) ≤ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      fun _ => True := latO_le _ _ _ _ fun _ _ => trivial
  have fix : ∀ u ∈ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S), heisO c.ψ s.V s'.V u p.f = p.f → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hθ _ _ _ _ p.f hpt u
      (GlobalTheory.VacGood.infPart_latO (hle hu)) h0 φ
  have hsph := hp.pre.sph
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) :=
    ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hsph.1 u hu),
      fun e he u hu hh => fix u hu (hsph.2 e he u hu hh)⟩
  refine ⟨hF.1, hF, hS, fun v hv => ⟨hF.1, ?_, ?_⟩⟩
  · intro u hu
    exact hS.1 u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu)
  · intro e he u hu hh
    exact hS.2 e he u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu) hh

end
