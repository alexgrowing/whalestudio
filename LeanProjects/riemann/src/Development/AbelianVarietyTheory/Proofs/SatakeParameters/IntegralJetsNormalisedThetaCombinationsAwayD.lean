import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDiscStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFramesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

theorem jets_comb {K : Type} [NormedField K] [IsUltrametricDist K] {X κ : Type} [Fintype κ] (r : κ → K)
    (sg : κ → MvPowerSeries X K) (hr : ∀ k, ‖r k‖ ≤ 1) (hsg : ∀ k, JetsIntegral (sg k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * sg k) := by
  refine (Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_
  refine Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_
  exact Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k))
    ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((TaylorLogMetric.embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem norm_natCast_coprime {p : ℕ} [Fact p.Prime] {n : ℕ} (h : Nat.Coprime n p) : ‖(n : ℂ_[p])‖ = 1 := by
  have e : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p]) := (map_natCast _ n).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem atLin_X {σ κ : Type} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) F = Formalism.L2.Th1.G.linSub c F := rfl

theorem tauEmb_eq {D : D7} {p : ℕ} [Fact p.Prime] {lm : TaylorLogMetric.Qbar →+* ℂ_[p]} {ι : ℂ ≃+* ℂ_[p]}
    (hι : Formalism.L2.KerInert.IotaExt lm ι) (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.tauEmb D lm τ x = ι (TaylorLogMetric.embT D τ x) := by
  have h := embT_mem D τ x
  show TaylorLogMetric.lamC lm (TaylorLogMetric.embT D τ x) = _
  rw [TaylorLogMetric.lamC, dif_pos h]
  exact (hι ⟨_, h⟩).symm

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem analytic_U (B : Base D cc δ) (t : TaylorLogMetric.VC D N N') {G : TaylorLogMetric.VC D N N' → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (TaylorLogMetric.U D B.tor t G) Set.univ := by
  have hadd : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => z + t) Set.univ := fun z _ => by fun_prop
  have h1 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => G (z + t)) Set.univ :=
    hG.comp hadd (fun _ _ => Set.mem_univ _)
  let ℓ : TaylorLogMetric.VC D N N' →ₗ[ℂ] ℂ := (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N').flip t
  have h2 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => ℓ z) Set.univ :=
    (LinearMap.toContinuousLinearMap ℓ).analyticOnNhd _
  have h3 : ∀ z : TaylorLogMetric.VC D N N', TaylorLogMetric.Hf D B.tor z t = ℓ z := fun z => by
    show _ = formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' z t
    rw [formV_apply]; rfl
  intro z hz
  have h4 : AnalyticAt ℂ (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) z := by
    have := h2 z hz
    fun_prop
  have h5 := (h1 z hz).mul h4
  have e : TaylorLogMetric.U D B.tor t G = (fun z => G (z + t)) * (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) := by
    funext z
    simp only [TaylorLogMetric.U, h3, Pi.mul_apply]
  rw [e]
  exact h5

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem term_jets (hIn : GlobalTheory.ThLoc.Inputs) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {X : Fields} (s : Seam D X) (hs : s.Ok)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁') {p : ℕ} [Fact p.Prime] (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁')
    (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) (hι : Formalism.L2.KerInert.IotaExt lm ι)
    (hpd : p ≠ D.host.d) (h3 : p = 3 → D.host.d % 3 = 2)
    (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t)
    {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (hy : ∀ j, y j ∈ TaylorLogMetric.YYl D L L') :
    JetsIntegral (TaylorLogMetric.atLin (fun k j => TaylorLogMetric.tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j)
      (TaylorLogMetric.pSer D lm (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')))) := by
  obtain ⟨s₁, hs₁, e1, e2⟩ := id hE
  obtain ⟨s₂, hs₂, e3, e4⟩ := id hE'
  have hS : Nat.Coprime (s₁ * s₂) p := Nat.Coprime.mul_left hs₁ hs₂
  obtain ⟨M, hM0, hMc, hMm⟩ := (Formalism.L2.KerInert.pairing_fact D cc δ p N N' L L₁ L' L₁' hE hE').2 t ht
  have hLat := GlobalTheory.T.normalisedThetaFamily_normalised_all_places D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L₁ L₁' hA₁ p ι

  have hθ := hLat.mem_th.1
  have hEan : AnalyticOnNhd ℂ (B.eNat χ N N' L₁ L₁') Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) Set.univ :=
      (LinearMap.toContinuousLinearMap (s.flatV N N').symm.toLinearMap).analyticOnNhd _
    have h2 := hθ.comp h1 (fun _ _ => Set.mem_univ _)
    have e : (B.eNat χ N N' L₁ L₁') = (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) ∘ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) := by
      funext w
      simp
    rw [e]
    exact h2
  have hGan := analytic_U B t hEan
  have hCo : TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')) TaylorLogMetric.Qbar :=
    hIn.algT D cc δ B χ hcc hδ hχ N N' L₁ L₁' hA₁ t ⟨M, hM0, hMm⟩

  have hU : (fun z => TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁') (s.flatV N N' z)) =
      Formalism.L2.Th1.H.opU (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) ((s.flatV N N').symm t)
        (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) := by
    funext z
    rw [KS.opU_pb (s.flatV N N') _ _ (KS.form_flat s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))), LinearEquiv.apply_symm_apply]
    simp only [Formalism.L2.Th1.H.opU, formV_apply]
    rfl

  let v : Fin n → DVar X.Tau N N' → ℂ := fun j =>
    (s.flatV N N').symm (TaylorLogMetric.embV D B.tor (((s₁ * s₂ : ℕ) : D.host.E) • y j))
  let A : Fin n → Fin n → ℂ_[p] := fun j x => if j = x then (((s₁ * s₂ : ℕ) : ℂ_[p]))⁻¹ else 0
  have hn1 : ‖(((s₁ * s₂ : ℕ) : ℂ_[p]))‖ = 1 := norm_natCast_coprime hS
  have hn0 : (((s₁ * s₂ : ℕ) : ℂ_[p])) ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  have hv : ∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) (s.laF B.tor L₁ L₁') (v j) := by
    intro j ω hω
    show s.flatV N N' (ω • v j) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
    rw [map_smul, LinearEquiv.apply_symm_apply]
    refine AddSubgroup.subset_closure ⟨ω, ?_, _, Formalism.L2.KerInert.ie_yy_scale s₁ s₂ e2 e3 (hy j), rfl⟩
    show ω ∈ TaylorLogMetric.lamOf D cc δ
    rw [← hlat]
    exact hω
  have hA : ∀ j x, ‖A j x‖ ≤ 1 := by
    intro j x
    by_cases h : j = x
    · simp only [A, if_pos h, norm_inv, hn1, inv_one, le_refl]
    · simp only [A, if_neg h, norm_zero, zero_le_one]
  have hfr : (fun (i : DVar X.Tau N N') x => (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : Fin n) =>
      TaylorLogMetric.tauEmb D lm k.1 (y j k.2.1 k.2.2)) (s.iT i.1, i.2) x) = frameM (ι : ℂ →+* ℂ_[p]) v A := by
    funext i x
    have e : v x i = ((s₁ * s₂ : ℕ) : ℂ) * TaylorLogMetric.embT D (s.iT i.1) (y x i.2.1 i.2.2) := by
      show TaylorLogMetric.embT D (s.iT i.1) ((((s₁ * s₂ : ℕ) : D.host.E) • y x) i.2.1 i.2.2) = _
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast]
    simp only [frameM, A, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [tauEmb_eq hι, e]
    simp only [RingHom.coe_coe, map_mul, map_natCast]
    field_simp
  have key := GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hlat (DVar X.Tau N N')
    (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L₁ L₁')
    (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) p ι hLat hpd h3 Unit (fun _ => 1)
    (fun _ => (s.flatV N N').symm t) M (fun _ => by simp) hM0
    (fun h => by
      have := Nat.Coprime.eq_one_of_dvd hMc.symm h
      exact (Fact.out : p.Prime).one_lt.ne' this)
    (fun _ => by
      show s.flatV N N' ((M : ℂ) • (s.flatV N N').symm t) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
      rw [map_smul, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
      exact hMm)
    (Fin n) v hv (Fin n) A hA
  rw [GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor D X s N N' p lm ι hι _ hGan hCo (Fin n), hfr, hU]
  simpa [thetaLin] using key

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

theorem GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → TaylorLogMetric.JetsInt D lm (TaylorLogMetric.YYl D L L') F := by
  intro hIn D cc δ hcc hδ B χ hχ X s hs N N' L L' hA p _ lm hpd h3 F hF
  obtain ⟨ι, hι⟩ := hIn.lamExt p lm
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd : 0 < D.host.d := hdp.pos
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd hd8 hdp B.L (GlobalTheory.FourthRootStd.hst B)
  have hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by
    rw [hL]
    exact B.lat
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL1, rfl⟩ := hF
  refine (GlobalTheory.T.latticeJetsIntegral_iff_integralFrames D N N' p lm _ _).1.2 fun n y hy => ?_
  have e : ∀ (c : D.what₂.Tau × Fin N' × Fin N → Fin n → ℂ_[p]) (G : Fin m → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j)
        (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) * G k) =
      ∑ k, MvPowerSeries.C (r k) * TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) (G k) := by
    intro c G
    rw [GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.atLin_X, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, Formalism.L2.Th1.G.linSubHom_apply]
    rfl
  rw [e]
  exact GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jets_comb r _ hr fun k =>
    GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.term_jets hIn hcc hδ B χ hχ s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat (hL1 k).1 (hL1 k).2.1 (hL1 k).2.2 lm ι hι hpd h3
      (t k) (ht k) y hy
