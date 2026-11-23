import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepFockVectorsSphericalOffSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.ExactNS

variable {D : D7}

theorem petersson_conj (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (X : Set (GA D V))
    (hX : IsFundamentalDomain (GQ V) X ν)
    (f g : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h) (hg : ∀ γ ∈ GQ V, ∀ h, g (γ * h) = g h) :
    GlobalTheory.Cusp.petersson V ν (fun h => conj (f h)) (fun h => conj (g h)) = conj (Lift.pet ν X f g) := by
  haveI := hν
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun h => conj (f h) * conj (conj (g h))) := fun γ hγ h => by
    simp only [hf γ hγ, hg γ hγ]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => conj (f h) * conj (conj (g h))) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  unfold Lift.pet
  rw [← integral_conj]
  simp only [map_mul]

theorem up_conj {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (hν : s.ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ s.V) s.fd s.ν) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (hF : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g) :
    GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = fun h => conj (p.up φ F h) := by
  haveI := hν
  funext h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθl : ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g)) := fun γ hγ x => by
    simp only [hθl γ hγ, hF γ hγ]
  simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ s.V) _ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ s.V) s.ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj]

theorem up_leftInv {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : ∀ γ ∈ GQ s'.V, ∀ h, p.up φ F (γ * h) = p.up φ F h := by
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθr : ∀ g, ∀ γ ∈ GQ s'.V, ∀ h, thetaKO p.ω g (γ * h) (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro g γ hγ h
    have e : ((g, γ * h) : GA D s.V × GA D s'.V) = (1, γ) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut 1 (one_mem _) γ hγ _ (hp.weil.om_pres _ _ hΦ)
  intro γ hγ h
  simp only [Step.up, hθr _ γ hγ]

theorem stepExactNS : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  intro D hHF hSoft hPeel hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC u₁ u₂ B hB hQ hNS l hl
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsF⟩ := id hs
  obtain ⟨hr', -, hs'F⟩ := id hs'
  have hv : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hRC.1, rfl⟩
  by_cases h0 : PiTensorProduct.tprod ℂ v = 0
  · have hz : ∀ g, zReal p m X φ v g = 0 := by
      intro g
      have hp0 := hMet.pure v v
      simp only [h0, map_zero, LinearMap.zero_apply] at hp0
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 hp0.symm
      have h0τ : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := inner_self_eq_zero.1 hτ
      simp only [zReal]
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [h0τ, inner_zero_left])]
      simp
    simp [h0, hz, Step.up, Lift.pet]
  have hF₁ : PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) ≠ 0 := fun h =>
    hB.1 ((hSoft c w hw k hk.le s hs).2.2.1 u₁ _ h0 h)
  have hparF : ParFun c s (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) B := hB.2 _ hF₁
  have hFlat := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw k hk.le s hs hr
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc k hk.le _ hsF
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc (k + 1) hk _ hs'F
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split D c (k + 1) _ hk hs'F
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS D hgap c w hw k hk s s' hs hs' p hp
  set F₁ := PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) with hF₁def
  set F₂ := PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v) with hF₂def
  have hu1 : (fun g => conj (F₁ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₁.1, hFlat u₁.2⟩ _ hv
  have hu2 : (fun g => conj (F₂ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₂.1, hFlat u₂.2⟩ _ hv
  have hrk0 : s.V.rank = D.R.rankY k := hsF.rank
  have hrk1 : s'.V.rank = D.R.rankY (k + 1) := hs'F.rank
  have hr1 : 1 ≤ s.V.rank := by
    rw [hrk0]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht2 : 2 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hrk1, hrk0]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      m X :=
    { setting := ⟨hr1, by omega, hrk, hc.inf, hsF.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hsF.selfDual, hs'F.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2.1, (hfock φ).2.1⟩
  have hsph : GlobalTheory.Core.Rk.IP.SphFun s.V s.Λ c.S (fun g => conj (F₂ g)) := by
    obtain ⟨-, hoffS, -⟩ := GlobalTheory.ChainOnto.LevelFacts.levFacts D c hc k hk.le _ hsF
    have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 (hFlat u₂.2))
    intro v' hv' κ hκ g
    obtain ⟨hκL, hκχ⟩ := hoffS v' hv' κ hκ
    have e : F₂ = PiTensorProduct.lift.symm (u₂ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    simp only [e]
    have hlev := hT.lev v _ hκL g
    rw [hκχ, one_mul] at hlev
    exact congrArg (starRingEnd ℂ) hlev
  have hIM : IsMajOf c s a := ⟨hmaj, hmaj_eq⟩
  obtain ⟨s₁, hs₁, hLI⟩ := hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC a hIM
  obtain ⟨hLint, hLeq⟩ := hLI u₁ u₂
  have hint : ∃ z : ℝ, z < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m X s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) z) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    refine ⟨max s₁ ((D.R.t : ℝ) / 2 - 1 / 2), max_lt hs₁ (by linarith), ?_⟩
    exact (hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv _
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (hLint _ (le_max_left _ _))).1
  have hPt := hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv ((D.R.t : ℝ) / 2)
    (by linarith) (hLint _ hs₁.le)
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    m X hPair ht2 (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hsF.haar hs'F.haar
    _ hu1 _ hu2 B hparF hsph hNS hint
  have key := hval l hl
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (((D.R.t : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hI : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g ∂s.ν =
      locQ c w k * ((∫ g, zReal p m X φ v g ∂mR) * conj (ip u₁ u₂)) := by
    rw [← hLeq, ← hPt.2 rfl]
    change _ = ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, flatInt p m X a φ F₁ F₂ (((D.R.t : ℝ) / 2 : ℝ) : ℂ) g ∂s.ν
    congr 1
    funext g
    simp only [flatInt]
    rw [← hsZ]
    exact (GlobalTheory.Core.Rk.IP.integrand_sZero (A := s.V) (B := s'.V) p.ω s.ν m X s.Λ a (p.pt φ) (p.pt φ) _ _ g).symm
  have hFl : ∀ F : GA D s.V → ℂ, (fun g => conj (F g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA →
      ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun F hF γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hF.1.1.left γ hγ g)
  rw [ExactNS.up_conj p hp hsF.haar hsF.fund φ F₁ (hFl F₁ hu1), ExactNS.up_conj p hp hsF.haar hsF.fund φ F₂ (hFl F₂ hu2),
    ExactNS.petersson_conj s'.V s'.ν hs'F.haar s'.fd hs'F.fund _ _ (ExactNS.up_leftInv p hp φ F₁)
      (ExactNS.up_leftInv p hp φ F₂), hI] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [Complex.conj_conj] at key'
  change Lift.pet s'.ν s'.fd _ _ = _
  rw [key']
  simp only [dS, map_mul, Complex.conj_conj]
  ring

end GlobalTheory.ChainTw.ExactNS

end
