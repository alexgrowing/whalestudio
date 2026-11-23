import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNegatedSpaceDiscreteSeriesModelTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowArrow

variable {D : D7}

theorem unit_of_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    IsUnit b.det := by
  have hJ : IsUnit (Formalism.REAL.Jm ε).det := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
  rw [← h, det_mul] at hJ
  exact isUnit_of_mul_isUnit_right hJ

theorem inv_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    (b⁻¹)ᴴ * Formalism.REAL.Jm ε * b⁻¹ = G := by
  have hb := unit_of_gram h
  have h1 : (bᴴ)⁻¹ * bᴴ = 1 := nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hb.star)
  have h2 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  rw [← h, conjTranspose_nonsing_inv]
  calc (bᴴ)⁻¹ * (bᴴ * G * b) * b⁻¹ = ((bᴴ)⁻¹ * bᴴ) * G * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_frame (V : HSp D) (c b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ c τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ A : Fr V, A.cart = c ∧ A.onb = b := by
  choose ε hε using h
  refine ⟨⟨ε, fun τ => (b τ)⁻¹, fun τ => isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 (unit_of_gram (hε τ).1)),
    fun τ => inv_gram (hε τ).1⟩, ?_, ?_⟩
  · funext τ
    simp only [Fr.cart]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1), ← (hε τ).2, Matrix.mul_assoc,
      mul_nonsing_inv _ (unit_of_gram (hε τ).1), Matrix.mul_one]
  · funext τ
    simp only [Fr.onb]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1)]

theorem lifts_neg {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    (hP : PairLifts D X) (hE : PairEx) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {A B : HSp D} {S S' : D.what₂.Tau → SPar} (MA : DSModel A S) (MB : DSModel B S') {aS aT : D.what₂.Tau → ℚ}
    (hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ) (aS τ) (aT τ)) (FA : Fr A) (FB : Fr B)
    (hA : cart MA = FA.cart) (hB : cart MB = FB.cart) {ω : GlobalTheory.Grid.WRep (GlobalTheory.Grid.sgn true B) A}
    (hω : IsWeilExp ψ (GlobalTheory.Grid.sgn true B) A aS aT ω) {f₀ : WO (GlobalTheory.Grid.sgn true B) A → ℂ}
    (hf₀ : IsVacF ψ θ (frSgn true FB) FA f₀) (h0 : f₀ ≠ 0) {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν) :
    ∃ It : PolF D A.rank B.rank → SmT MA → SmT MB, ∀ f, IsVacF ψ θ (frSgn true FB) FA f →
      LiftsM θ MA MB ν 𝓕 (fun P h g => thetaKO ω ((GlobalTheory.Grid.ofSgn true B).symm h) g (ptF ψ θ (frSgn true FB) FA f P)) It := by
  obtain ⟨N, κ, hN⟩ := GlobalTheory.negModel_tr D θ hθ B S' MB
  have cS : ∀ τ, (Fr.ofModel N).cart τ = (frSgn true FB).cart τ := fun τ =>
    (hN.cart τ).trans ((congrArg _ (congrFun hB τ)).trans (cart_frSgn true FB τ).symm)
  have cT : ∀ τ, (Fr.ofModel MA).cart τ = FA.cart τ := fun τ => congrFun hA τ
  have vac : ∀ f, IsVacF ψ θ (frSgn true FB) FA f → IsVacF ψ θ (Fr.ofModel N) (Fr.ofModel MA) f :=
    fun f h => ⟨h.1, fun τ => by rw [cS, cT]; exact h.2 τ⟩
  obtain ⟨j, hj⟩ := GlobalTheory.FrameChange.ptF_frame_change D ψ θ hψ hθ (GlobalTheory.Grid.sgn true B) A _ _ _ _ cS cT
  obtain ⟨It, hIt⟩ := hE D _ S aS aT hR _ A N MA θ ψ hθ
  have hv : IsVacVec ψ θ N MA f₀ := ⟨hf₀.1, h0, (vac f₀ hf₀).2⟩
  refine ⟨fun P v => κ (It (j P) v), fun f hf F hF => ?_⟩
  obtain ⟨F₁, hF₁, e₁⟩ := hP _ _ aS aT (fun τ => GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 (hR τ)) _ A N MA θ ψ hθ ω hω f₀ It hv
    (hIt ω hω f₀ hv) ν 𝓕 hν h𝓕 f (vac f hf) F hF
  obtain ⟨F', hF', e'⟩ := hN.mult' F₁ hF₁
  refine ⟨F', hF', fun P v h => ?_⟩
  have := e₁ (j P) v ((GlobalTheory.Grid.ofSgn true B).symm h)
  rw [← ptF_ofModel, e'] at this
  simp only [hj f hf.1 P, MulEquiv.apply_symm_apply, RingHom.id_apply] at this
  exact this

theorem cen_eq (τ : D.what₂.Tau) : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
  funext i
  unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
  rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
  rfl

theorem parRow_eq (i : ℕ) (τ : D.what₂.Tau) : parRow D 1 i τ = GlobalTheory.Grid.parV D i 0 τ := by
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [cen_eq, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [GlobalTheory.Grid.parV, hg]
  rfl

theorem exp_att {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {c : ℚ} (h : HasInfExp D χ τ c)
    (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) : HasInfExp D (Lift.attChr χ η n) τ (att c n) := by
  unfold Lift.attChr att
  split_ifs
  · rw [sub_eq_add_neg]
    exact StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)
  · exact h

end GlobalTheory.RowArrow

open GlobalTheory.RowArrow in

theorem GlobalTheory.RowArrow.rowStep : GlobalTheory.FunPr.Hypotheses₂ → PairEx → RowModels → RowStep := by
  intro pr hE _ D _ hS T L μ0 hL sc hc G W M hM i hi S S' MA MB e e' cA cB
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ :=
    GlobalTheory.RealPlaceTheta.exists_record_theta_all pr.discreteSeriesCover pr.harishChandraModules
  have I := GlobalTheory.PairLift.inputs_of_chosenSeries pr.discreteSeriesCover pr.harishChandraModules pr.cuspRapidDecay pr.casselmanWallach D X hX
  have hP := GlobalTheory.PairLift.RuleLift.pairLifts D X I (GlobalTheory.PairLift.cuspAll_of_lowAll D X I
    (GlobalTheory.PairLift.lowAll_of_lowFock D X I (GlobalTheory.LowerMembersRule.lowFock D X I)))
  have rA : (Node.grid i 0).InRange D.R.m := ⟨hi.le, Nat.zero_le _⟩
  have rB : (Node.grid (i + 1) 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
  obtain ⟨FA, a1, a2⟩ := exists_frame _ _ _ (W.onb_is _ rA)
  obtain ⟨FB, b1, b2⟩ := exists_frame _ _ _ (W.onb_is _ rB)
  have b3 : (frSgn true FB).cart = G.cartS W.cart (.chi i 0) := funext fun τ => by
    rw [cart_frSgn, b1]; rfl
  have b4 : (frSgn true FB).onb = G.onS W.onb (.chi i 0) := b2
  have hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ)
      (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0)) (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) :=
    fun τ => by
      rw [e, e', hc, parRow_eq, parRow_eq]
      exact GlobalTheory.GridParD.pairPar_X D hS i 0 τ hi (Nat.zero_le _)
  have hη : ∀ τ, HasInfExp D L.eta τ (1 / 2) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have hχ : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => GlobalTheory.Grid.cen D τ (D.R.m - i)) (G.ch.chi_eq _ (by omega) (by omega))
      ⟨_, fun τ => by simp only [cen_eq, hc]; push_cast; rfl, G.ch.inf _ (by omega) (by omega)⟩ τ
  have hω : IsWeilExp W.ψ (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) 0))) (G.V (.grid i 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) (W.om (.chi i 0)) := by
    refine ⟨_, _, W.om_is (.chi i 0) rB, fun τ => ⟨?_, ?_⟩⟩
    · have r : (G.pS (.chi i 0)).rank = GlobalTheory.Grid.rkV D (i + 1) 0 := (node_isV G hL rB).rank
      rw [GridData.chrS, r]
      exact exp_att (hχ τ) (hη τ) _
    · have r : (G.pT (.chi i 0)).rank = GlobalTheory.Grid.rkV D i 0 := (node_isV G hL rA).rank
      rw [GridData.chrT, r]
      exact exp_att (hχ τ) (hη τ) _
  have hv := (W.vac_is i hi).2
  have v0 : IsVacF W.ψ W.θ (frSgn true FB) FA (W.vac i) := ⟨hv.theta, fun τ => by rw [b3, a1]; exact hv.fock τ⟩
  have n0 : W.vac i ≠ 0 := fun h => by
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
    have := h2 p hp
    simp [nrm2, h] at this
  have v1 : ∀ κ, IsVacF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) := fun κ => by
    obtain ⟨u, hu, h⟩ := W.cosVec_is
    have th := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) hv.theta
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hu
    refine ⟨th, fun τ => ?_⟩
    rw [b3, a1]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (h i hi κ) hv.theta th
      (hv.fock τ)
  obtain ⟨hν, h𝓕⟩ := (hM.row i hi.le).haar_fund
  obtain ⟨It, hIt⟩ := lifts_neg h3 h4 h5 hP hE W.θ_is W.ψ_std MA MB hR FA FB (cA.trans a1.symm) (cB.trans b1.symm) hω v0 n0 hν h𝓕
  refine ⟨It, fun F hF κ => ?_⟩
  obtain ⟨F', hF', h⟩ := hIt _ (v1 κ) F hF
  have ef : ∀ P, ptF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) P = W.fock (.chi i 0) (W.cosVec i κ) P := fun P => by
    unfold ptF
    rw [b3, b4, a1, a2]
    rfl
  simp only [ef] at h
  exact ⟨F', hF', fun P v => ⟨fun g => (h P v g).1, funext fun g => (h P v g).2⟩⟩

end
