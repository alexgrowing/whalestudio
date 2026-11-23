import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTeichmullerOfFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

noncomputable section

namespace GlobalTheory.HWL.IoLayer

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem sepRA' (LL : FinExt l) (e : OCb l) (he : ¬ IsUnit (e - 1)) (t : RA LL)
    (ht : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e = t) (x : RA LL)
    (hx : ∀ k, (t - 1) ^ k ∣ x) : x = 0 := by
  refine sepRA LL e he x ?_
  have h := tmul_sub_one LL (WittVector.teichmuller l e)
  rw [h, ht]
  exact hx

theorem teich_pow (LL : FinExt l) (e : OCb l) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (e ^ l) : RA LL) =
      ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e) ^ l := by
  have h1 : WittVector.teichmuller l (e ^ l) = (WittVector.teichmuller l e : Ainf l) ^ l := map_pow _ _ _
  rw [h1, Algebra.TensorProduct.tmul_pow, one_pow]

theorem γ₀_X_eq {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL} (R : WSer Γ)
    (g : ↥(GK K)) (c : ℤ_[l]) (hc : (c : ℚ_[l]) = (P.χQ g : ℚ_[l])) :
    R.γ₀ (Γ.resΓ g) X = PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL)) (binomialSeries ℤ_[l] c) - 1 := by
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  obtain ⟨_, _, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hlin : (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) c := by
    apply Subtype.ext
    have := Γ.χΓ_res g
    rw [P.PD_χ, ← hc] at this
    exact this
  have hact := (GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (R.γ₀ (Γ.resΓ g)) R.φ₀ c h0
    (R.γ₀_comm _) (R.γ₀_X _).1 ((R.γ₀_X _).2.trans hlin)).2
  rw [hact, (GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l ↥(OL LL)).1, GlobalTheory.Cyc.cyc]

set_option maxHeartbeats 1000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∃ I : IoS AI R, IoW I := by
  intro l _ P AI K s LL hG Γ R
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨u, hu, huniq⟩ := GlobalTheory.UnramIdem.exists_prod_hom l P K s LL hG Γ.emb Γ.emb_bij
  have he := εroot_sub_not_unit AI s
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 _ he
  obtain ⟨io, hπ, hc⟩ := let_exists
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1) : RA LL) u
  have hπ' := hπ.trans (tmul_sub_one LL _)
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  have h1 : io.comp (letφ R.φ₀) = (φRA LL).comp io := by
    have ht := teich_pow LL (AI.εroot s)
    have he' : ¬ IsUnit (AI.εroot s ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    refine comm_φ l R.φ₀ h0 io u hc (φRA LL) _ hπ' ((φRA_teich LL _).trans ht) ?_
      (sepRA' LL _ he' _ ht)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := hu (c ^ l) m hm hl
      (by rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm, pow_mul, hcm, one_pow]) (xb ^ l)
      (tilt_pow hxb l) (shift _ _ o) (fun i => by
        have := DFunLike.congr_fun (Γ.emb_σ (i - 1)) c
        rw [sub_add_cancel, AlgHom.comp_apply, sigma_root K c m hm hl hcm] at this
        rw [this]
        exact ho (i - 1))
    exact e2.trans ((congrArg (φRA LL) e1).trans (φRA_teich LL xb)).symm
  have h2 : ∀ g : ↥(GK K), io.comp (letγ (R.γ₀ (Γ.resΓ g))) = (gRA AI LL (g : GQ l)).comp io := by
    intro g
    obtain ⟨χ, hχ, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
    obtain ⟨⟨io0, hio0, -⟩, -⟩ := GlobalTheory.Cyc.IoMap.main l _ he
    have he' : ¬ IsUnit (AI.actT g (AI.εroot s) - 1) := fun h => he (by
      have := h.map (AI.actT g).symm
      rwa [map_sub, map_one, RingEquiv.symm_apply_apply] at this)
    have e0 := (io_zl LL _ _ he io hπ io0 hio0 (binomialSeries ℤ_[l] (χ g : ℤ_[l]))).trans
      (congrArg (fun w : Ainf l => ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RA LL))
        (io_binomial AI s g _ (hχ g) io0 hio0))
    refine comm_γ _ _ (γ₀_X_eq R g _ (hχ g)) io u hc (gRA AI LL g) _ _ hπ' e0 (gRA_teich AI LL g _) ?_
      (sepRA' LL _ he' _ rfl)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := actT_tilt AI g c (g.2 ⟨c, c.2.1⟩) m hm hl xb hxb
    have e3 := gRA_teich AI LL g xb
    rw [e2] at e3
    exact e1.trans ((congrArg (gRA AI LL g) e1).trans e3).symm
  obtain ⟨I, hI⟩ := assemble R (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) _
    (φRA LL) (fun g : ↥(GK K) => gRA AI LL (g : GQ l)) (inclR_φRA LL) (fun g => inclR_gRA AI LL g)
    (by rw [P.PD_p]; exact (GlobalTheory.HWL.TensorWitt.main l LL).1) io hπ
    (isUnit_inclR LL _ (εroot_ne_one AI s)) h1 h2
  refine ⟨I, fun c m hm hl hcm xb hxb o ho => ?_⟩
  rw [hI, ← cst_apply, hc]
  exact hu c m hm hl hcm xb hxb o ho

end GlobalTheory.HWL.IoLayer
