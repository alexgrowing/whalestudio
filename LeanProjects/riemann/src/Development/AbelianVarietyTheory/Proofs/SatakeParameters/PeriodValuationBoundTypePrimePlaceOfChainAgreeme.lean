import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundOfJetLoss
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRatIdxOfJetsRatDeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBoundStatement
import Formalism.LocalToGlobal.Divisibility.BrJoint

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriodTies

theorem boundAt_of_chainTie (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D)
    (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (eta : Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Integrality) (hJ : JetLossAll D EX sel B χ cD) (hC : 1 ≤ C1)
    (hH : HostTie EX) (hCT : CharTie Ch mu0 eta sel) (hA : AnTie D δ χ cD) (i : Fin 2) (hS : SizeAt D i)
    (w : LiftErrorLocal.Pl D) (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hCh : ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ) :
    BoundAt L EX C1 i w u μ := by
  classical
  obtain ⟨-, hTied, -, hsel⟩ := hCT
  obtain ⟨ξ, cst, I, hI, b, hY, hK, hF, hP, eM, jA, -, -, hrat, hcol, hrow, hper⟩ := hCh
  rintro φ hφ F ⟨c, hc⟩
  have hX := hH.2.2.2.1.ok
  have hPr := hH.2.2.2.2
  obtain ⟨hne, hloss⟩ := vG_loss_le L EX hPr i w hw u
  choose! x hx using hrow.2.2.1
  have hxF : jA (∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.OtoLL (c v) • x v) = F := by
    rw [hc, map_sum]
    exact Finset.sum_congr rfl fun v hv => by rw [LinearMap.map_smulₛₗ, hx v hv]; rfl
  have hxM := (hrow.2.2.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, hxF.trans hc⟩
  refine ⟨_, (hxF ▸ hper φ _).symm, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hg : ((D.host.g i : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
    refine mem_of_vAdd_pos _ ?_
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero)] at h1
    have h2 : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by exact_mod_cast h1
    have h3 : (((D.host.g i : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.host.g i : D.what₂.LL) := map_natCast (algebraMap _ _) _
    rw [h3, h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hTS : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hgS : ∀ k, (recPrimes EX).g k ∈ badS D := fun k => by
    fin_cases k <;> simp [badS, hostS]
  have hb : 2 * (recFields D).f * D.R.N D.R.m + 1 < D.host.g i := by
    rw [show (recFields D).f = D.R.f from D.what₂.card_Tau]
    exact hS.1
  have hdeg : ∀ j < D.R.m, (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 1 < (D.host.g i : ℤ) := by
    intro j hj
    have h1 := (hS.2 u (j + 1) (Finset.mem_Icc.2 ⟨by omega, hj⟩)).1
    have h2 : LiftErrorLocal.Dpi D u (j + 1) = ((∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun τ _ => partitionSize D EX u j hj τ
    have h3 := Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj τ
    rw [h2] at h1
    have h4 : 2 * (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 2 < (D.host.g i : ℤ) := by exact_mod_cast h1
    omega
  have hcolb := colMu_bound_all (recWts EX) Ch sel ξ cst I _ (hJ hH hsel hA) GlobalTheory.JetOpWeylLat.jetOpWeyl chainWeights stdMove levelPrimes
    (scalarUnit_of levelPrimes heckeUnit twistUnit) entryAtG (EntQ.entryAtQ volumeAtQ) TopTwist.topAtQ hX hPr hsel u hTS hgS hI
    hTied b hY (Formalism.L2.Col.rPsymF Ch) hK hF i (D.plEq w) hg
    (fun j hj b' => wtUnit_chF (recWts EX) sel ξ I hX u hF (hPr.g_prime i) hb _ hg hj b') hdeg hrat _ ((hcol φ).1 hφ)
  have hm := GlobalTheory.BranchMembers.members _ _ _ (recWts EX) (recWts_ok EX) u
  have hval := valuation_PtilE_le_one (recWts EX) Ch sel ξ hX hPr hsel u hTS (hB _ _ _ _ _ _ _) (fun τ => (hm τ).1)
    (fun τ => (hm τ).2) (Formalism.L2.Col.rPsymF Ch) hP (hPr.g_prime i) (hPr.T_ne_g u i) hb (D.plEq w) hg
    ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) • _) hcolb _ hxM
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hval
  suffices key : ∀ y : D.what₂.LL, (D.plEq w).valuation D.what₂.LL
      ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) * y) ≤ 1 →
      y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y from key _ hval
  intro y hval
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  have hc0 := Finset.prod_ne_zero_iff.2 fun j (_ : j ∈ Finset.range D.R.m) => hne j
  have h1 := vAdd_nonneg_of_le _ (mul_ne_zero hc0 hy) hval
  rw [vAdd_mul_of_ne _ hc0 hy] at h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h2 : 0 ≤ LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) + LiftErrorLocal.vG D w y := by
    unfold LiftErrorLocal.vG
    rw [← add_div]
    exact div_nonneg (by exact_mod_cast h1) he.le
  have h3 : 0 ≤ LiftErrorLocal.errC D L := by
    have := L.etaSz_pos.le
    unfold LiftErrorLocal.errC
    positivity
  nlinarith

theorem boundAt_of_ties : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup),
    TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word,
      D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  intro hJS D L EX Dx μ ⟨Ch, mu0, eta, sel, δ, B, χ, cD, hH, hCT, hA, hCh⟩ i hS w hw u _
  have hJ : JetLossAll D EX sel B χ cD := GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound hJS D EX sel δ B χ cD
  exact boundAt_of_chainTie D L EX Dx Ch mu0 eta sel B χ cD 1
    (GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs) hJ le_rfl
    hH hCT hA i hS w hw u μ (hCh u)

end GlobalTheory.ColPeriodTies

end
