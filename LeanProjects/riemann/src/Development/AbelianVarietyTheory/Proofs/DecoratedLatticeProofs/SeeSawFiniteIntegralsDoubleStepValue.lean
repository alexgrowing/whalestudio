import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFlatMapIndepUnfoldingStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawCommonRealDatumBiThetaVacuumContractionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegrandVacuumFormBasePointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalizedHaarPairAtFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValFin

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun _ _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => by simp only [Pi.zero_apply]; exact contDiff_const⟩

theorem isLatVac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) :
    IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩

theorem isReal_zero (c : Comm D) (j : ℕ) : c.IsReal j 0 := by
  refine ⟨⟨continuous_const, fun v => ⟨isThetaFunO_zero _ _ _, isLatVac_zero _ _ _ _⟩,
    fun u => ⟨isThetaFunO_zero _ _ _, isLatVac_zero _ _ _ _⟩⟩, ?_⟩
  intro n L L' _ _ _ _ u v
  simp only [Pi.zero_apply]
  exact contDiff_const

theorem isAutFun_rTrans {V : HSp D} (x : GA D V) {φ : GA D V → ℂ} (h : IsAutFun V φ) :
    IsAutFun V (rTrans x φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  refine ⟨fun γ hγ g => ?_, ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩, ?_⟩
  · simp only [rTrans, mul_assoc]; exact h.left γ hγ (g * x)
  · have hc : Continuous fun k : GA D V => x⁻¹ * k * x := by fun_prop
    exact hU.preimage hc
  · have hk' : x⁻¹ * k * x ∈ U := by simpa [MulAut.conj_apply] using hk
    have hf : x⁻¹ * k * x ∈ GfC V := by
      unfold GfC at hkf ⊢
      rw [MonoidHom.mem_ker] at hkf ⊢
      simp [hkf]
    have e : g * k * x = g * x * (x⁻¹ * k * x) := by group
    simp only [rTrans]
    rw [e, hUφ _ hk' hf]
  · exact h.cont.comp (continuous_mul_right x)

theorem trc_mapDomain {V : HSp D} (ε : GA D V →₀ ℂ) (b : GA D V) (f : GA D V → ℂ) :
    trc (ε.mapDomain (· * b)) f = trc ε (rTrans b f) := by
  unfold trc
  change (ε.mapDomain (· * b)).sum (fun g c => c • rTrans g f) = ε.sum (fun g c => c • rTrans g (rTrans b f))
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  funext z
  simp [rTrans, mul_assoc]

end GlobalTheory.ValFin

namespace GlobalTheory.ValFin

variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (Q : Pl D → Prop) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT Q f := by
  have key := (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hstd S T Q (fun p => ¬ Q p) (fun p hp hn => hn hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => Q p ∨ ¬ Q p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  rw [e] at key
  exact (key.1 hf).1

theorem ctr_indep (c : Comm D) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (s₁ s₁' : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h))
    (s₂ s₂' : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ)
    (h₁ : IsThetaFunO c.ψ _ _ Ψ₁) (h₂ : IsThetaFunO c.ψ _ _ Ψ₂) :
    c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂ = c.ctr j σ h s₁' s₂' Ψ₁ Ψ₂ := by
  unfold Comm.ctr
  rw [(GlobalTheory.T.theta_flatMap_indep_unfoldingStep D c.ψ).1 _ _ _ s₁ s₁' Ψ₁ h₁, (GlobalTheory.T.theta_flatMap_indep_unfoldingStep D c.ψ).2 _ _ _ s₂ s₂' Ψ₂ h₂]

theorem valX : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → v.Is →
    (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → ContrLaw D → FlatLaw D → BiAct D → ValX t := by
  intro D c v 𝒯 t w hc hv ht hL hContr hFlat hBi
  intro j σ h P₁ P₂ a ha a' ha'
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  have hV₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (v.Ψ j P₁ 1 a) :=
    hv.Ψ j hj1 P₁ 1 (one_mem _) a ha
  have hV₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) (v.Ψ (j + 1) P₂ a a') :=
    hv.Ψ (j + 1) hj2 P₂ a ha a' ha'
  by_cases hT : Nonempty 𝒯
  swap
  · exact ⟨0, isReal_zero c j, fun s => (hT ⟨s⟩).elim⟩
  obtain ⟨s₀⟩ := hT
  refine ⟨(v.op j).app c.ψ (c.ctr j σ h ((t s₀).sBF j (σ + 1) h) ((t s₀).sFB j σ h) (v.Ψ j P₁ 1 a) (v.Ψ (j + 1) P₂ a a')),
    ((GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction D c v (t s₀) (w s₀) hc hv (ht s₀) (hL s₀).vac (hL s₀).tl hFlat).1 j σ h _ _ hV₁ hV₂).2, ?_⟩
  intro s ψ hψ y G x
  have hLs := hL s
  have hF := hLs.form
  have hj2m : j + 2 ≤ D.R.m := by omega
  have hφR : ∀ α, (t s).rd j α ψ y ∈ v.RamAd j := fun α => (hF.rd j hj2m ψ hψ α y).1
  have hφX : ∀ α, (t s).rd j α ψ y ∈ (w s).FX j α := fun α => (hF.rd j hj2m ψ hψ α y).2.1
  have hφS : ∀ α, (t s).rd j α ((t s).S j ψ) y = v.Sad j ((t s).rd j α ψ y) := fun α => (hF.rd j hj2m ψ hψ α y).2.2
  have hφA : ∀ α, IsContAut _ ((t s).rd j α ψ y) := fun α => (hv.ram j _ (hφR α)).1
  have hFaut : IsAutFun _ (G.1 x) := by
    obtain ⟨J, χ, hJ⟩ := (ht s).CC (j + 1 + 1) hj2
    exact (GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp c.θ (c.M (j + 1 + 1)) J χ G.1 (hJ G.2) x).1.toIsAutFun
  have hfaut : IsAutFun _ (rTrans (a' * v.b (j + 1 + 1)) (G.1 x)) := isAutFun_rTrans _ hFaut
  have hfY : rTrans (a' * v.b (j + 1 + 1)) (G.1 x) ∈ (w s).FY (j + 1 + 1) := (hF.row (j + 1 + 1) hj2 G x a' ha').1
  obtain ⟨ρ₁, μ₁, hn₁⟩ := GlobalTheory.T.exists_normalizedHaarPair_at_finitePlaces D (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (GlobalTheory.jacGrp_isClosed _ _ _ _ _)
    (v.N (j + 1)) (hv.sd (j + 1) hj1) (w s).Q
  obtain ⟨ρ₂, μ₂, hn₂⟩ := GlobalTheory.T.exists_normalizedHaarPair_at_finitePlaces D (c.V (j + 1 + 1))
    (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
    (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) (v.N (j + 1 + 1)) (hv.sd (j + 1 + 1) hj2) (w s).Q
  have hdisj : ∀ p, p ∈ v.gP → ¬ p ∈ (w s).Q := fun p hp hq => Finset.disjoint_left.mp hF.disjG hq hp
  have K₁ := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (· ∈ (w s).Q) hdisj
  have K₂ := GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V (j + 1)) (c.V (j + 1 + 1)) (· ∈ v.gP) (· ∈ (w s).Q) hdisj
  have hVQ₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ (w s).Q) (comb c.ψ _ _ (v.eG j) (v.Ψ j P₁ 1 a)) :=
    (K₁.2.1 (v.eG j) (hv.atG j).1).2 _ _ _
      (vac_of_all hc.std (hv.sd j (by omega)) (hv.sd (j + 1) hj1) _ hV₁)
  have hVQ₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ (w s).Q) (comb c.ψ _ _ (v.eG (j + 1)) (v.Ψ (j + 1) P₂ a a')) :=
    (K₂.2.1 (v.eG (j + 1)) (hv.atG (j + 1)).1).2 _ _ _
      (vac_of_all hc.std (hv.sd (j + 1) hj1) (hv.sd (j + 1 + 1) hj2) _ hV₂)
  have hQ := hLs.ql j σ h ρ₁ μ₁ ρ₂ μ₂ hn₁ hn₂ _ _ hVQ₁ hVQ₂ (fun α => (t s).rd j α ψ y)
    (fun α => ⟨hφA α, hφX α⟩) _ hfaut hfY
  have hc₁ := K₁.1 (v.eG j) ((w s).eQ j) (hv.atG j).1 (hF.atQ j).1 (v.Ψ j P₁ 1 a)
  have hc₂ := K₂.1 (v.eG (j + 1)) ((w s).eQ (j + 1)) (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 (v.Ψ (j + 1) P₂ a a')
  rw [← hc₁, ← hc₂] at hQ
  have hcell := GlobalTheory.T.seeSawDoubleStep_finiteIntegral_collapse_twistPlaces D c v (t s) (w s) hc hv (ht s) hF hLs.weil hLs.off hLs.gs hLs.qfin hContr hFlat j σ h
    ρ₁ μ₁ ρ₂ μ₂ hn₁ hn₂ _ _ hV₁ hV₂ (fun α => (t s).rd j α ψ y) hφR G x a' ha' _ rfl _ hQ
  have hmove := GlobalTheory.T.seeSaw_iteratedIntegrand_vacuumForm_base_points D c v (t s) (w s) hc hv (ht s) hF j σ h P₁ P₂ a ha a' ha' (fun α => (t s).rd j α ψ y)
    (G.1 x) _ _ _ _ rfl rfl rfl hcell
  convert hmove using 1
  have hrhs := GlobalTheory.T.seeSaw_unfoldedData_eq_kernelData_at_level D c v (t s) (w s) hc hv (ht s) hF hLs.gv hLs.tl hFlat hBi j σ h _ _ hV₁ hV₂
    (fun α => (t s).rd j α ψ y) hφR
  have hct := ctr_indep c j σ h ((t s).sBF j (σ + 1) h) ((t s₀).sBF j (σ + 1) h) ((t s).sFB j σ h) ((t s₀).sFB j σ h)
    _ _ hV₁.1 hV₂.1
  rw [hct] at hrhs
  beta_reduce at hrhs
  have hper : ∀ (k : ℂ) φ' f', (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (k • φ') f' =
      k * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ φ' f' := by
    intro k φ' f'
    have := (GlobalTheory.HandHom.hand_hom D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      ((t s).sBF j (σ + 1) h) ((t s).sFB j σ h) (c.lnk j σ h) (c.vL j σ h) 0).2.2 k 1 φ' f'
    rwa [one_smul, mul_one] at this
  have htwo : (fun α => (t s).rd j α ((t s).S j ψ) y) = fun α => v.Sad j ((t s).rd j α ψ y) := funext hφS
  have hcomm : v.b (j + 1 + 1) * a' = a' * v.b (j + 1 + 1) :=
    GlobalTheory.FinTranslate.comm_fin_real _ (hv.b (j + 1 + 1)) ha'
  have htrc : ∀ β, trc ((t s).e (j + 1 + 1) β) (rTrans a' (G.1 x)) =
      trc ((w s).ε (j + 1 + 1) β) (rTrans (a' * v.b (j + 1 + 1)) (G.1 x)) := by
    intro β
    rw [(hF.e (j + 1 + 1) β).1, trc_mapDomain]
    congr 1
    funext z
    simp only [rTrans, mul_assoc, hcomm]
  rw [hLs.cv.1 j σ h]
  unfold Tup.perF
  rw [htwo]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hrhs β, hper, htrc β]
  ring

end GlobalTheory.ValFin
