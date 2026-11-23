import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ActEEqOfConjRelated
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open PositivityTheory.Member.ZakTransform GlobalTheory.CompanionTheory.Ar.SvN GlobalTheory.EmbChart

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}

theorem schr_inst (ψ : AddChar (Fv F v) ℂ) :
    @schr _ _ (invTwo v) ψ κ _ = @schr _ _ (invTwoV (v := v)) ψ κ _ := by
  rw [Subsingleton.elim (invTwo v) invTwoV]

theorem ad_heis (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (hw : At (evFin F v) w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (@schr _ _ (invTwo v) (psiV ψ v) κ _ (locW v w) φ) := by
  intro r hr
  rw [schr_inst, schr_tens ψ _ _ (indep_of hr.1), offP_eq, sub_smul, (at_iff _).1 hw, one_smul, sub_self, schr_zero]
  rfl

theorem ad_rest (r : (κ → AF F) → ℂ) (φ₀ : (κ → Fv F v) → ℂ) (hne : φ₀ ≠ 0) (hr : Rest (evFin F v) φ₀ r)
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) : Rest (evFin F v) φ r := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  let S : Module.End ℂ ((κ → Fv F v) → ℂ) := (LinearMap.proj y : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ).smulRight ((φ₀ y)⁻¹ • φ)
  have h := lift_mem (v := v) (S := S) (fun θ _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hφ)) hr.2
  rw [lift_tens _ _ (indep_of hr.1)] at h
  have e : S φ₀ = φ := by
    change φ₀ y • (φ₀ y)⁻¹ • φ = φ
    rw [smul_smul, mul_inv_cancel₀ hy, one_smul]
  exact ⟨hr.1, e ▸ h⟩

theorem ad_act (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (s : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F))
    (L L' : Module.End ℂ ((κ → Fv F v) → ℂ)) (sv : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ (s w) (T Φ))
    (h4 : ∀ φ ∈ SB (κ → Fv F v), L φ ∈ SB (κ → Fv F v) ∧ L' φ ∈ SB (κ → Fv F v) ∧ L' (L φ) = φ ∧ L (L' φ) = φ)
    (h5 : ∀ w, ∀ φ ∈ SB (κ → Fv F v), L (@schr _ _ (invTwo v) (psiV ψ v) κ _ w φ) =
      @schr _ _ (invTwo v) (psiV ψ v) κ _ (sv w) (L φ))
    (h6 : ∀ w, locW v (s w) = sv (locW v w) ∧ At (evFin F v) (s w - w)) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ (c • L φ) := by
  have hA := isCharAF_of_isStd hψ
  have hc : Continuous (psv v ψ) := hA.1.comp cont_at
  rw [schr_inst] at h5
  have hL' : ∀ φ ∈ SB (κ → Fv F v), L' φ ∈ SB (κ → Fv F v) := fun φ h => (h4 φ h).2.1
  obtain ⟨x₀, hx₀⟩ := hA.2.2.2
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.AdelicSchur.schur F κ ψ hA.1 (fun e => hx₀ (by rw [e]; rfl)) hA.2.2.1 (lift v L' * T)
    (fun Φ hΦ => lift_mem hL' (h1 Φ hΦ)) (fun l hl => h2 _ (lift_adm hL' l hl)) fun w Φ hΦ => by
      rw [Module.End.mul_apply, Module.End.mul_apply, h3 w Φ hΦ]
      refine lift_schr ψ ?_ (fun φ hφ => ?_) (h1 Φ hΦ)
      · rw [offP_eq, offP_eq, ← sub_eq_zero, ← smul_sub, sub_smul, one_smul, (at_iff _).1 (h6 w).2, sub_self]
      · have e := h5 (evP v w) _ (hL' φ hφ)
        rw [(h4 φ hφ).2.2.2] at e
        have e2 : evP v (s w) = sv (evP v w) := (h6 w).1
        rw [e2]
        exact (congrArg L' e).symm.trans (h4 _ (schr_mem_SB hc _ (hL' φ hφ))).2.2.1
  refine ⟨a, fun φ hφ r hr => ?_⟩
  have e := congrArg (lift v L) (ha _ hr.2)
  rw [Module.End.mul_apply, lift_lift (S'' := 1) hL' (fun θ h => (h4 θ h).2.2.2) (h1 _ hr.2), lift_one, map_smul,
    lift_tens _ _ (indep_of hr.1)] at e
  rw [e]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem indep_at {r : (κ → AF F) → ℂ} (h : Indep v r) (x z : κ → AF F) (hz : At (evFin F v) z) : r (x + z) = r x := by
  have e : z = fun i => atPlace v (evFin F v (z i)) := funext fun i => by
    rw [← ep_mul]; exact (congrFun ((at_iff z).1 hz) i).symm
  rw [e]; exact h x _

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open GlobalTheory.DiagForm Classical in
theorem lDiag_box_ne : ∃ f : SInf F κ, lDiag F κ (boxFun (pure f (stdF κ)) (pure f (stdF κ))) ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  let f : SInf F κ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨f, ?_⟩
  have hm := pure_mem f (good_std (F := F) (κ := κ))
  have hg := pf_mem (good_std (F := F) (κ := κ))
  set g := pf (stdF (F := F) κ) with hgd
  have g01 : ∀ y, g y = 0 ∨ g y = 1 := fun y => by
    obtain ⟨S, hS⟩ := exists_fin (good_std (F := F) (κ := κ)).2 y
    rw [hgd, pf_eq_prod S y hS]
    refine Finset.prod_induction _ (fun z : ℂ => z = 0 ∨ z = 1) ?_ (Or.inr rfl) fun u _ => ?_
    · rintro a c (rfl | rfl) (rfl | rfl) <;> simp
    · simp only [stdF, Set.indicator_apply]
      split_ifs <;> simp
  have g0 : g 0 = 1 := by
    rw [hgd, pf, finprod_eq_one_of_forall_eq_one]
    intro u
    simp [stdF, Set.indicator_apply]
  have e : resD F κ (boxFun (pure f (stdF κ)) (pure f (stdF κ))) =
      fun p => (((b (eI F κ p.1)) ^ 2 : ℝ) : ℂ) * ((‖g p.2‖ : ℝ) : ℂ) := funext fun p => by
    have e1 : pure f (stdF κ) (glue p) = (b (eI F κ p.1) : ℂ) * g p.2 := by
      change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _)) * g p.2 = _
      simp only [RingEquiv.apply_symm_apply]
      rfl
    change pure f (stdF κ) (glue p) * pure f (stdF κ) (glue p) = _
    rw [e1]
    rcases g01 p.2 with h | h <;> simp [h, sq]
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hm _ hm)), e, mu,
    integral_prod_mul (fun u => (((b (eI F κ u)) ^ 2 : ℝ) : ℂ)) (fun y => ((‖g y‖ : ℝ) : ℂ)), integral_complex_ofReal,
    integral_complex_ofReal]
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt ?_)) (Complex.ofReal_ne_zero.2 (ne_of_gt ?_))
  · refine ((b.continuous.comp (eI F κ).continuous).pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      ?_ (fun u => sq_nonneg _) ?_
    · exact (b.hasCompactSupport.comp_homeomorph (eI F κ).toHomeomorph).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    · simp only [Function.comp_apply, map_zero]
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
      simp
  · exact hg.1.continuous.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) hg.2.norm
      (fun _ => norm_nonneg _) (by simp [g0])

open Classical in
theorem adjoint_statement : AdSt where
  psi F _ _ ψ h := by
    have hA := isCharAF_of_isStd h
    obtain ⟨x₀, hx₀⟩ := hA.2.2.2
    refine ⟨fun e => hx₀ (by rw [e]; rfl), fun v => ⟨hA.1.comp cont_at, fun e => ?_⟩⟩
    obtain ⟨y, hy⟩ := ((GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hA).1 v).2
    exact hy (DFunLike.congr_fun e y)
  Heisenberg₂ F _ _ κ _ ψ v w hw φ := ad_heis ψ w hw φ
  rest F _ _ κ _ v r φ₀ _ hne hr φ hφ := ad_rest r φ₀ hne hr φ hφ
  act F _ _ κ _ ψ hψ v T s L L' sv := ad_act ψ hψ T s L L' sv
  diag F _ _ κ _ ψ v := by
    obtain ⟨f, hf⟩ := lDiag_box_ne (F := F) (κ := κ)
    have hi := indep_pure (v := v) f (stdF (F := F) κ)
    have e : tens (evFin F v) (stdF κ v) (pure f (Function.update (stdF κ) v 1)) = pure f (stdF κ) := by
      rw [← pure_update f (good_std (F := F) (κ := κ)).2, Function.update_eq_self]
    have hm := pure_mem f (good_std (F := F) (κ := κ))
    refine ⟨_, GlobalTheory.DiagForm.lDiag_adm, fun x y Φ hΦ => GlobalTheory.DiagForm.lDiag_schr ψ x y hΦ, stdF κ v, stdF_mem v,
      pure f (Function.update (stdF κ) v 1), ⟨indep_at hi, e ▸ hm⟩, ⟨fun x z hz => ?_, ?_⟩, e ▸ hf⟩
    · have h1 := indep_at hi (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
      have h2 := indep_at hi (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
      exact congrArg₂ (· * ·) h1 h2
    · have := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hm _ hm
      rw [← e] at this
      convert this using 1
      funext x
      exact mul_mul_mul_comm _ _ _ _

end PositivityTheory.KCo
