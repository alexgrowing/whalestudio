import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepVanOfStepX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevChiWithPOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

variable {D : D7}

theorem pt_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : PolF D T.rank S.rank) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ = ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pt_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {k : GA D S}
    (hk : k ∈ GfC S) (φ : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (om (k, 1) f) φ = om (k, 1) (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f hf φ).2.symm

theorem lift_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {ι : Type} [Fintype ι] (κ : ι → GA D S) (hκ : ∀ i, κ i ∈ GfC S) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hf' : f' = ∑ i, (a i)⁻¹ • om (κ i, 1) f) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (F : GA D T → ℂ) (φ : PolF D T.rank S.rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) 𝓕 ν) (U : GA D S → ℂ)
    (hU : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f φ) F g = U g)
    (hl : ∀ i g, U (g * κ i) = a i * U g) :
    (∀ g, IntegrableOn (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h) 𝓕 ν) ∧
      liftS om ν 𝓕 F (pureTensorO ψ θ S T sS sT BS BT f' φ) = (Nat.card ι : ℂ) • U := by
  have e : ∀ g h, thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h =
      ∑ i, (a i)⁻¹ * (thetaKO om (g * κ i) h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) := fun g h => by
    rw [hf', (pt_sum hom.std hθ sS BS sT BT _ _ _ (fun i => hom.om_pres _ _ hf) φ).2]
    unfold thetaKO
    rw [map_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pt_om hom hθ sS BS sT BT hf (hκ i), map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Module.End.mul_apply, ← map_mul,
      Prod.mk_mul_mk, mul_one]
  refine ⟨fun g => ?_, funext fun g => ?_⟩
  · simp only [e]
    exact integrable_finset_sum _ fun i _ => (hi _).const_mul _
  · show ∫ h in 𝓕, thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h ∂ν = _
    simp only [e]
    rw [integral_finset_sum _ fun i _ => (hi _).const_mul _]
    have : ∀ i, ∫ h in 𝓕, (a i)⁻¹ * (thetaKO om (g * κ i) h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) ∂ν = U g := fun i => by
      rw [integral_const_mul]
      have h1 := hU (g * κ i)
      unfold Lift.liftInt at h1
      rw [h1, hl, ← mul_assoc, inv_mul_cancel₀ (ha i), one_mul]
    simp only [this, Finset.sum_const, Finset.card_univ, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem levChi_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ) (p : P.H)
    {κ : GA D V} (hκ : IsLevelLift V β L p.1 κ) : κ ∈ levS V β (withP L P) :=
  ⟨hκ.1, hκ.2.1, by
    show rTup β L (finE V κ) ∈ P.H
    rw [hκ.2.2]; exact p.2⟩

theorem step_eigen {S T : HSp D} {Sp : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hCR : GlobalTheory.Published.CuspRapidDecay) {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f : WO S T → ℂ} (hpt : ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P))
    {M : DSModel S Sp} {β : GL (Fin S.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ S.rank} (hL : flag1L L = L)
    {μ : Measure (GA D S)} {𝓔 : Set (GA D S)} (hμ : μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ S) 𝓔 μ)
    {Ds : Type} [AddCommGroup Ds] [Module ℂ Ds] {It : PolF D T.rank S.rank →ₗ[ℂ] Ds →ₗ[ℂ] SmT M} (hIt : It ≠ 0)
    {CC : Submodule ℂ (Ds →ₗ[ℂ] (GA D T → ℂ))} (hCC : ∀ F : CC, ∀ v, ∀ γ ∈ GQ T, ∀ g, F.1 v (γ * g) = F.1 v g)
    {β' : GL (Fin T.rank) (Lev.EAf D)} {L' : LevDat D.host.E ℂ T.rank}
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hν : ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ T) 𝓕 ν)
    {io : CC →ₗ[ℂ] MultT θ M (levS S β L) (levChi S β L)}
    (hio : Lift.IsIo ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f) It CC _ io)
    {g0 : G0 L.Pg L.r} {κ : GA D S} (hκ : IsLevelLift S β L g0 κ) {g0' : G0 L'.Pg L'.r} {κ' : GA D T}
    (hκ' : IsLevelLift T β' L' g0' κ') {a' : ℂ} (hf : (levChi S β (flagL L) κ)⁻¹ • om (κ, κ') f = a' • f)
    (F : CC) {c : ℂ} (hF : ∀ v h, a' * F.1 v (h * κ') = c * F.1 v h) (v : SmT M) (g : GA D S) :
    (levChi S β (flagL L) κ)⁻¹ * (io F).1 v (g * κ) = c * (io F).1 v g := by
  have := GlobalTheory.ChainEquiv.step ψ θ hθ χS χT om hom sS BS sT BT f hpt M β L hL μ hμ.1 𝓔 hμ.2 (GlobalTheory.MultFinite.schurMult hCR _ _)
    It hIt CC hCC β' L' ν hν.1 𝓕 hν.2 io hio g0 κ hκ g0' κ' hκ' a' hf F (c • F) (fun v h => (hF v h).symm) v g
  rw [← this, map_smul]
  rfl

end GlobalTheory.Fam.Inhab

end
