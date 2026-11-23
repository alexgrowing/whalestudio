import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomEquiv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeTranslationOperatorEqPhaseMulNegComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LawsAndChart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentMeasureNormLeOneIffLatticeIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedVectorTranslatesPrimeOrderIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLiftStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransportStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePairStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsThetaStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicJetsOfAlgebraicTaylorStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicDirectionScaledEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLiftsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimePowSmulGoodLiftMemSetupLatticeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefInWeilOperatorTranslateAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOnPadicIntOfEqOnNaturalsMomentStatement

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomFin

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem U_transport (D : D7) (T : Tor D) {N N' g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf Hm (e x) (e y) = Hf D T x y) (t : VC D N N') (F : VC D N N' → ℂ) :
    JMB.opU Hm (e t) (fun z => F (e.symm z)) = fun z => U D T t F (e.symm z) := by
  funext z
  have h1 : JMB.hf Hm z (e t) = Hf D T (e.symm z) t := by
    rw [← hhf]; simp
  simp only [JMB.opU, U, map_add, ContinuousLinearEquiv.symm_apply_apply, h1, hhf]
  congr 2
  ring

theorem wop_transport (D : D7) (T : Tor D) {N N' g : ℕ} (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D T x y) (hd : S.d = D.host.d) (p : ℕ) [Fact p.Prime]
    (y t : VC D N N') (F : VC D N N' → ℂ) (hq : ∃ m : ℤ, (JMB.beta S.d S.Hm (e y) (e y)).re = m) :
    JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) (fun z => F (e.symm z))) =
      fun z => Wop D T p y (U D T t F) (e.symm z) := by
  obtain ⟨m, hm⟩ := hq
  have hqH : qH D T y = (JMB.beta S.d S.Hm (e y) (e y)).re := by
    rw [qH, JMB.beta, hhf, hd, Complex.re_ofReal_mul]
  have hU := U_transport D T S.Hm e hhf t F
  have hUy := U_transport D T S.Hm e hhf y (U D T t F)
  funext z
  rw [JMB.opW, hU, Wop, I3.JetMomEq.wPh_of_int T y m (hqH.trans hm), hqH]
  rw [hUy]

theorem jet_transport (D : D7) {N N' g : ℕ} (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (G : VC D N N' → ℂ)
    (hG : ContDiff ℂ ⊤ G) (k : ℕ) (v : Fin k → VC D N N') :
    JMB.jetV (fun z => G (e.symm z)) (fun j => e (v j)) = iteratedFDeriv ℂ k G 0 v := by
  have h := (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N').iteratedFDeriv_comp_right hG (0 : Fin g → ℂ) (i := k) le_top
  simp only [JMB.jetV]
  rw [show (fun z => G (e.symm z)) = G ∘ (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N') from rfl, h]
  simp

theorem embV_sum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ} (a : Fin r → ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i, ((a i : ℕ) : D.host.E) • b i) = ∑ i, ((a i : ℕ) : ℂ) • embV D (tor0 D cc δ) (b i) := by
  funext τ i j
  simp [embV, tor0, Finset.sum_apply, Matrix.sum_apply, map_sum]

theorem kap_transport (D : D7) (T : Tor D) {N N' g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf Hm (e x) (e y) = Hf D T x y) (x y : VC D N N') : kap D T x y = JMB.kap Hm (e x) (e y) := by
  simp only [kap, JMB.kap, hhf]

theorem moments_fin : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p → ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω) := by
  intro hMv hAlg D cc δ B χ hcc hδ hχ p _ lam hp2 hjac hcop
  obtain ⟨hdp, hd16, -, -, -⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  have hSplit : GlobalTheory.MomOne.Split D.host.d p := Or.inr ⟨hp2, hjac⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam
  obtain ⟨δ₀, θ, Ω, hPer⟩ := GlobalTheory.MomN.exists_per D.host.d p ι hdp hd16 hSplit
  obtain ⟨hTh, h12, hδ₀, hAll, hΩ, hLaws, hPerM⟩ := hPer
  obtain ⟨hQ, hUn⟩ := GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hcc hδ h12 p hp2 hcop
  have hne : δ / δ₀ ≠ 0 := by
    intro h; have := hUn ι; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
  have hδ0 : δ ≠ 0 := by intro h; apply hne; rw [h, zero_div]
  have hlam : lamC lam (δ / δ₀) = ι (δ / δ₀) := by rw [lamC, dif_pos hQ]; exact (hι ⟨_, hQ⟩).symm
  refine ⟨Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀), ?_, ?_⟩
  · rw [norm_mul, norm_mul, hΩ, hlam, hUn ι, GlobalTheory.MomOne.Basic.norm_nat_eq_one (Nat.Coprime.symm hcop)]
    norm_num
  intro N N' L L' hA t ht
  obtain ⟨g, S, e, hSd, hSok, hLa, hhf, hbeta, hLaRep, hNN⟩ := GlobalTheory.T.exists_analyticSetup_periodLatticePair D cc δ B hcc hδ N N' L L' hA
  obtain ⟨N₀, hN₀, hN₀p, hN₀t⟩ := ht
  have hHm : S.Hm.IsHermitian := hSok.2.2.1.1
  have hd0 : 0 < S.d := hSd ▸ hdp.pos
  have hH := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hd0 hHm
  refine ⟨N₀, hN₀p, fun r b hb => ?_⟩
  set F := B.eNat χ N N' L L' with hFdef
  set e' : (Fin g → ℂ) → ℂ := fun z => F (e.symm z) with he'
  have hTheta : S.IsTheta e' := GlobalTheory.T.normalizedThetaVector_isometry_isTheta D cc δ B χ hcc hδ hχ hδ0 N N' L L' hA g S e hSd hLa hhf
  have hF : ContDiff ℂ ⊤ F := by
    have : F = fun x => e' (e x) := by funext x; simp [e']
    rw [this]; exact hTheta.1.comp e.contDiff
  have hAlg0 : ∀ α, taylor D F α ∈ Qbar := by
    have := hAlg D cc δ B χ hcc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simp⟩
    simpa [U_zero] using this
  have hAJ : S.AlgJets δ₀ e' := GlobalTheory.T.algebraicJets_of_algebraic_taylor D cc δ δ₀ B N N' L L' F hQ hδ₀ hF hAlg0 g S e hLa hLaRep
  set bS : Fin r → Fin g → ℂ := fun i => e (δ • embV D B.tor (b i)) with hbSdef
  have hbS : S.NNBasis p bS := hNN p r b hcop hb
  have hN₀S : (N₀ : ℂ) • e t ∈ S.La := by
    rw [← map_smul, Nat.cast_smul_eq_nsmul, hLa]; exact hN₀t
  have ht' : S.PrimeTo p (e t) := ⟨N₀, hN₀, hN₀p, hN₀S⟩
  obtain ⟨Nμ, hμall⟩ := GlobalTheory.MomOne.Translates.moments_of_translates D.host.d p lam δ₀ θ ι Ω hdp hd16 hSplit hTh hδ₀
    hAll hι hΩ hLaws g S hSd hSok r bS hbS e' hTheta hAJ
  obtain ⟨μ, -, hM1⟩ := hμall (e t) ht'
  have hUt : JMB.opU S.Hm (e t) e' = fun z => U D B.tor t F (e.symm z) := U_transport D B.tor S.Hm e hhf t F
  have hUF : ContDiff ℂ ⊤ (U D B.tor t F) := by
    have : U D B.tor t F = fun x => JMB.opU S.Hm (e t) e' (e x) := by funext x; rw [hUt]; simp
    rw [this]; exact ((hH.2.2.1 (e t) e' hTheta.1).1).comp e.contDiff
  have hnorm : ‖μ‖ ≤ 1 := by
    have hG : ContDiff ℂ ⊤ (JMB.opU S.Hm (e t) e') := (hH.2.2.1 (e t) e' hTheta.1).1
    refine (GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral p ι lam δ₀ Ω g S r bS (e t) _ μ hι hδ₀ hΩ hSok (hSd ▸ hSplit) hbS ht' hG hM1).2 ?_
    rw [hUt]
    have hE := GlobalTheory.T.normalizedVector_translates_prime_order_integral hMv D cc δ B hcc hδ p hp2 hjac hcop ι δ₀ θ Ω ⟨hTh, h12, hδ₀, hAll, hΩ, hLaws, hPerM⟩ χ hχ
      N N' L L' hA t ⟨N₀, hN₀, hN₀p, hN₀t⟩
    exact GlobalTheory.T.latticeJetsAreBoundedMoments_pullback p ι (VC D N N') (Fin g → ℂ) _ (La D B.tor L L') S.La.toAddSubgroup
      (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N') (U D B.tor t F) hUF
      (fun x hx => ⟨1, Nat.coprime_one_left _, by
        rw [one_smul, ← hLa]; simpa using hx⟩) hE
  refine ⟨μ, hnorm, fun n y hy => ?_⟩
  have hyS := GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts D cc δ N N' L L' g S e p lam N₀ n hSd hLa y hy
  obtain ⟨hqy, m, eps, yt, hId, hm, hIm, hW, hK⟩ :=
    GlobalTheory.T.goodLift_eq_idempotent_lift p lam g S r bS e' (e t) hSok (hSd ▸ hSplit) hbS hTheta N₀ hN₀ hN₀p hN₀S n (e y) hyS
  set G := Wop D B.tor p y (U D B.tor t F) with hGdef
  have hWt : JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) e') = fun z => G (e.symm z) :=
    wop_transport D B.tor S e hhf hSd p y t F hqy
  have hGc : ContDiff ℂ ⊤ G := by
    have : G = fun x => JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) e') (e x) := by funext x; rw [hWt]; simp
    rw [this]; exact ((hH.2.2.1 (e y) _ (hH.2.2.1 (e t) e' hTheta.1).1).2).comp e.contDiff
  have hImLa : ∀ x ∈ La D B.tor L L', ∀ x' ∈ La D B.tor L L', ∃ k : ℤ, (Hf D B.tor x x').im = k := by
    intro x hx x' hx'
    obtain ⟨u, v, huv⟩ := hSok.2.2.2.2.2.2.1 (e x) ((hLa x).2 hx) (e x') ((hLa x').2 hx')
    exact ⟨v, by rw [← hhf]; exact hH.2.2.2.2.1 _ _ u v huv⟩
  have hyT : ∃ a : ℕ, 0 < a ∧ a • y ∈ La D B.tor L L' := by
    refine ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, ?_⟩
    rw [← hLa, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
    push_cast
    exact GlobalTheory.T.prime_pow_smul_goodLift_mem_setupLattice g S p lam N₀ n hSok (e y) hyS
  have hqH : ∃ m : ℤ, qH D B.tor y = m := by
    obtain ⟨z, hz⟩ := hqy
    refine ⟨z, ?_⟩
    rw [qH, ← hz, JMB.beta, hhf, hSd, Complex.re_ofReal_mul]
  have hCoef : CoefIn D G Qbar := GlobalTheory.T.coefIn_weilOperator_translate_algebraic D B.tor N N' F (La D B.tor L L') p y t hF
    (fun s hs α => hAlg D cc δ B χ hcc hδ hχ N N' L L' hA s hs α) ⟨N₀, hN₀, hN₀t⟩ hyT hImLa hqH
  refine ⟨hCoef, fun k y' gf hg => ?_⟩
  set ys : Fin k → Fin g → ℂ := fun j => (δ₀ / δ) • e (δ • embV D B.tor (y' j)) with hysdef
  have hys : ∀ j, S.AlgDir (ys j) := fun j => GlobalTheory.T.algebraicDirection_scaled_embedding D cc δ δ₀ B N N' L L' hcc hA hQ hne g S e hLa (y' j)
  have hdir : ∀ j, δ₀⁻¹ • ys j = e (embV D B.tor (y' j)) := by
    intro j
    simp only [ys, map_smul, smul_smul]
    rw [show δ₀⁻¹ * (δ₀ / δ * δ) = 1 by field_simp, one_smul]
  have hf := GlobalTheory.T.eq_on_padicInt_of_eq_on_naturals_moment p lam Ω g S r n k bS (JMB.liftY p n eps bS yt) ys gf (fun a => by
    rw [hg a, ← hK a, kap_transport D B.tor S.Hm e hhf, embV_sum]
    have hs : e (δ • ∑ i, ((a i : ℕ) : ℂ) • embV D (tor0 D cc δ) (b i)) = ∑ i, ((a i : ℕ) : ℂ) • bS i := by
      simp only [bS, Finset.smul_sum, map_sum, map_smul, smul_comm δ]
    rw [hs]
    congr 1
    exact Finset.prod_congr rfl fun j _ => (GlobalTheory.T.pairing_scaledDirections_eq_period_pairing D cc δ δ₀ B N N' g S e p lam Ω r b (y' j) _ hQ hne hcop hbeta).symm)
  obtain ⟨-, hμf⟩ := hM1 n m eps hId hm (fun _ i => hIm i) yt k ys hys gf hf
  rw [← hW, hWt] at hμf
  simp only [hdir] at hμf
  rw [jet_transport D e G hGc k] at hμf
  obtain ⟨-, hjet⟩ := GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport D cc δ p lam N N' G hGc hCoef k y'
  rw [hjet, ← hμf]
  rfl

end GlobalTheory.MomFin
