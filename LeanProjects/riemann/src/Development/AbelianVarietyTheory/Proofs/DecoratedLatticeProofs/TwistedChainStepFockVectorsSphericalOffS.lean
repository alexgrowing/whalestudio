import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem fock_sph_tw : ∀ D : D7, ForStepQ D fun c _ k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  classical
  intro D _ c w hw k hk s s' hs hs' p hp
  have hc : c.Is := hw.com
  obtain ⟨hr₁, hL, hfl⟩ := hs
  obtain ⟨hr₂, -, hfl'⟩ := hs'
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hrk : s.V.rank ≤ s'.V.rank := by
    have e1 : s.V.rank = D.R.rankY k := hfl.rank
    have e2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [e1, e2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  obtain ⟨hfθ, -, hfv⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hsd hsd' hrk hvec
  have hPS : ∀ PP ∈ s.L.Pg ∪ w.Q, PP.under (𝓞 D.host.F) ∈ c.S := by
    intro PP hPP
    rw [hL] at hPP
    have hPP' : PP ∈ c.Pg := by rw [hw.union]; exact hPP
    exact Finset.mem_image_of_mem _ hPP'
  refine ⟨fun φ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hfθ hfv φ
  · obtain ⟨hvac, e, he, hth⟩ := hvec
    exact GlobalTheory.FockSph.isLatVac_pureTensorO_off hθ (onb s.M) (onb s'.M) hvac he hth c.S hPS hp.theta φ
  · intro v hv
    obtain ⟨hf₀, e, he, hth⟩ := hvec
    obtain ⟨NS, hNS, hNSv⟩ := hfl.base
    obtain ⟨NT, hNT, hNTv⟩ := hfl'.base
    have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      obtain ⟨P, hP⟩ := GlobalTheory.ChainOnto.VacOffS.exists_under (D := D) v
      have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
      have h1 := hNSv P hPv
      have h2 := hNTv P hPv
      intro h
      rw [← hP] at h
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
      rw [map_natCast, Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact h1 h
      · exact h2 h
    have hle := GlobalTheory.ChainOnto.VacOffS.latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
    have hoff : ∀ PP ∈ s.L.Pg ∪ w.Q, PP.under (𝓞 D.host.F) ≠ v := by
      intro PP hPP h0
      exact hv (h0 ▸ hPS PP hPP)
    have hfix : ∀ u ∈ latO s.V s'.V (GlobalTheory.AdelicU.frameLat s.V : Set (Fin s.V.rank → D.host.E))
        (GlobalTheory.AdelicU.frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
        heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
        (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
          (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
    refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
    · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chS Lift.chrStep
    split_ifs <;> assumption
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chT Lift.chrStep
    split_ifs <;> assumption

end GlobalTheory.ChainTw

end
