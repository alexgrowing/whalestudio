import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymCollapseOfAllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllPositionsHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GValMid

theorem one_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))) f₁ f₂,
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = G.q.v) f₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (G.eg j) f₁) (comb c.ψ _ _ (G.eg (j + 1)) f₂) =
      C • biComb c.ψ _ _ _ (G.cg j) (G.cg (j + 1)) (c.ctr j σ h s₁ s₂ f₁ f₂) := by
  intro D c v G hc hv j σ h
  have hs := G.hs
  have H : j + 1 + 1 + 2 * σ = G.s := by omega
  obtain ⟨C, hC, key⟩ := GlobalTheory.LocMod.GValProof.gval_of_laws D (GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D))
    (GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)) (GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor)
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds) G.k G.ν G.unitVol (GlobalTheory.LocMod.ofSplit G.q) G.s D.R.k
    G.S (Fin D.R.t) c.ψ G.char j (2 * σ) H
  refine ⟨C, hC, fun s₁ s₂ f₁ f₂ h₁ h₂ => ?_⟩
  have a₀ : j + (2 * σ + 1 + 1 + 1) = G.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = G.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = G.s + 1 := by omega
  have hne : G.sc j ≠ 0 := fun e => by
    have := G.sc_unit j
    rw [e, map_zero] at this
    exact zero_ne_one this
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit G.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) _ _ _ (2 * σ) :=
    ⟨G.sc j, hne, G.FX j (by omega), G.FX (j + 1) (by omega), G.FX (j + 1 + 1) (by omega), G.FY j _ a₀, G.FY (j + 1) _ a₁,
      G.FY (j + 1 + 1) _ a₂, G.bes j (σ + 1) h _ a₀, G.jac j (σ + 1) h _ a₁,
      G.sc_step j ▸ G.bes (j + 1 + 1) σ (idx_step h) _ a₂⟩
  obtain ⟨T₁, m₁, e₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY j _ a₀) (G.FY (j + 1) _ a₁) c.ψ G.S.ψ hc.std G.char G.S.cond
    _ _ (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (G.latY j _ a₀) (G.latY (j + 1) _ a₁)).2 f₁ h₁
  obtain ⟨T₂, m₂, e₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY (j + 1) _ a₁) (G.FY (j + 1 + 1) _ a₂) c.ψ G.S.ψ hc.std G.char
    G.S.cond _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega)) (G.latY (j + 1) _ a₁) (G.latY (j + 1 + 1) _ a₂)).2 f₂ h₂
  obtain ⟨O₁, o₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, o₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have b₁ : j + (2 * σ + 1 + 1) = G.s := by omega
  have b₂ : j + 1 + (2 * σ + 1) = G.s := by omega
  have g₁ := (G.eg_is j _ b₁).2 T₁ m₁ O₁ ⟨_, (GModel.phi_sb G).1 j _ b₁⟩ o₁ rfl
  have g₂ := (G.eg_is (j + 1) _ b₂).2 T₂ m₂ O₂ ⟨_, (GModel.phi_sb G).1 (j + 1) _ b₂⟩ o₂ rfl
  have := key σ _ _ _ F s₁ s₂ (c.lnk j σ h) (c.vL j σ h) (G.cg j) (G.cg (j + 1)) (G.cg_mid j _ b₂) (G.cg_mid (j + 1) _ H)
    T₁ T₂ m₁ m₂ ⟨_, (GModel.phi_sb G).1 j _ b₁⟩ ⟨_, (GModel.phi_sb G).1 (j + 1) _ b₂⟩ O₁ O₂ rfl rfl o₁ o₂
  rw [← e₁ O₁ o₁, ← e₂ O₂ o₂, ← g₁, ← g₂]
  exact this

theorem vac_foldr : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∀ j, j + 1 + 1 ≤ D.R.m →
  ∀ (i : Fin n) (L : List (Fin n)), i ∉ L → ∀ Ψ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ →
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (L.foldr (fun i' f => comb c.ψ _ _ ((G i').eg j) f) Ψ) := by
  intro D c v n G hc _ hG j hj i L hi Ψ hΨ
  induction L with
  | nil => exact GlobalTheory.SeeSawRhs.vac_mono (fun p hp => (hG.places p).2 ⟨i, hp⟩) hΨ
  | cons a L ih =>
    have hs := (G a).hs
    have hai : (G a).q.v ≠ (G i).q.v := fun e => hi (by rw [hG.inj e]; exact List.mem_cons_self)
    have hat : CombAt (· = (G a).q.v) ((G a).eg j) := fun u hu r s => by
      rw [← ((G a).eg_is j ((G a).s - j) (by omega)).1 u hu r s]
      exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt (G a).q)
    exact ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = (G a).q.v) (· = (G i).q.v) fun p h1 h2 => hai (h1.symm.trans h2)).2.1 _ hat).2
      _ _ _ (ih fun hm => hi (List.mem_cons_of_mem _ hm))

section Alg

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} {ι : Type} (a : ι → WO A S →₀ ℂ) (b : ι → WO S A' →₀ ℂ)

theorem comb_foldr (d : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (L : List ι) (u : WO A S) (w : WO S A') :
    comb ψ S A' d (fun w' => L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => C u' w') u) w =
      L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => comb ψ S A' d (C u') w) u := by
  induction L generalizing u with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    refine (GlobalTheory.SeeSawRhs.comb_comm2 ψ A S A' (a i) d
      (fun u'' w' => L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => C u' w') u'') u w).trans ?_
    congr 1
    funext u''
    exact ih u''

theorem biComb_foldr (C : WO A S → WO S A' → ℂ) (L : List ι) (u : WO A S) (w : WO S A') :
    L.foldr (fun i C' => biComb ψ A S A' (a i) (b i) C') C u w =
      L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => L.foldr (fun i f => comb ψ S A' (b i) f) (C u') w) u := by
  induction L generalizing u w with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    unfold biComb
    congr 1
    funext u'
    refine Eq.trans ?_ (comb_foldr ψ a (b i) (fun u'' => L.foldr (fun i f => comb ψ S A' (b i) f) (C u'')) L u' w)
    congr 1
    funext w'
    exact ih u' w'

theorem theta_foldr (C : WO A S → WO S A' → ℂ) (hC : ∀ w, IsThetaFunO ψ A S fun u => C u w) (L : List ι) (w : WO S A') :
    IsThetaFunO ψ A S fun u => L.foldr (fun i f => comb ψ S A' (b i) f) (C u) w := by
  induction L generalizing w with
  | nil => exact hC w
  | cons i L ih => exact GlobalTheory.SeeSawRhs.theta_comb_left (fun u => L.foldr (fun i f => comb ψ S A' (b i) f) (C u)) ih (b i) w

variable {ψ}

theorem theta_left {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (w : WO S A') : IsThetaFunO ψ A S fun u => C u w := by
  obtain ⟨U, hU, hl⟩ := h.levL
  refine ⟨fun γ u => h.quasiL γ u w, ⟨U, hU, fun x hx h0 => hl x hx h0 w⟩,
    h.cont.comp (continuous_id.prodMk continuous_const), fun k L hL h0 u => ?_⟩
  simpa using h.smooth k L 0 hL continuous_const h0 (fun t => Matrix.map_zero _ (finPart D).map_zero) u w

theorem theta_right {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (u : WO A S) : IsThetaFunO ψ S A' (C u) := by
  obtain ⟨U, hU, hl⟩ := h.levR
  refine ⟨fun γ w => h.quasiR γ u w, ⟨U, hU, fun x hx h0 => hl x hx h0 u⟩,
    h.cont.comp (continuous_const.prodMk continuous_id), fun k L hL h0 w => ?_⟩
  simpa using h.smooth k 0 L continuous_const hL (fun t => Matrix.map_zero _ (finPart D).map_zero) h0 u w

end Alg

theorem biComb_dG : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j + 1 < D.R.m →
  ∀ C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ,
    (∀ w, IsThetaFunO c.ψ _ _ fun u => C u w) → (∀ u, IsThetaFunO c.ψ _ _ (C u)) →
    biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) C =
      (List.finRange n).foldr (fun i C' => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C') C := by
  intro D c v n G hG j hj C h₁ h₂
  funext u w
  rw [biComb_foldr, ← hG.dG j (by omega) _ (theta_foldr c.ψ (fun i => (G i).cg (j + 1)) C h₁ _ w)]
  unfold biComb
  congr 1
  funext u'
  rw [hG.dG (j + 1) hj _ (h₂ u')]

theorem gValue_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  intro D c v n G hc hv hG j σ h
  choose C hC key using fun i => one_place D c v (G i) hc hv j σ h
  refine ⟨((List.finRange n).map C).prod, List.prod_ne_zero fun h0 => ?_, fun s₁ s₂ Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
  · obtain ⟨i, -, hi⟩ := List.mem_map.1 h0
    exact hC i hi
  have ind : ∀ L : List (Fin n), L.Nodup →
      c.ctr j σ h s₁ s₂ (L.foldr (fun i f => comb c.ψ _ _ ((G i).eg j) f) Ψ₁)
          (L.foldr (fun i f => comb c.ψ _ _ ((G i).eg (j + 1)) f) Ψ₂) =
        (L.map C).prod • L.foldr (fun i C' => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C') (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      obtain ⟨hi, hL'⟩ := List.nodup_cons.1 hL
      simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [key i s₁ s₂ _ _ (vac_foldr D c v n G hc hv hG j (by omega) i L hi Ψ₁ h₁)
        (vac_foldr D c v n G hc hv hG (j + 1) (by omega) i L hi Ψ₂ h₂), ih hL', GlobalTheory.SeeSawRhs.biComb_smul, smul_smul]
  have hb : IsBiTheta c.ψ _ _ _ (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) :=
    (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hc.std _ _ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF s₁ Ψ₁) (flatFB s₂ Ψ₂)
      (((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).1 _ _ _ s₁).Heisenberg₂.theta _ h₁.1)
      (((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).2 _ _ _ s₂).Heisenberg₂.theta _ h₂.1)).1
  rw [hG.eG j (by omega) _ h₁.1, hG.eG (j + 1) (by omega) _ h₂.1, ind _ (List.nodup_finRange n),
    biComb_dG D c v n G hG j (by omega) _ (theta_left hb) (theta_right hb)]

end GlobalTheory.SeeSaw.GValMid

end
