import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStepA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStepB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh MIntegrable mInt logNormSec
  isPotential_ofFun mIntSymm mIntAdd mIntRsmul mIntLinear mIntNonneg mIntegrableCont
  logNormIntegrable poincareLelong byPartsSymm isPotentialRsmul)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell)

noncomputable section

theorem GreenMassStep.proof : GreenMassStep.Statement := by
  intro D W _ _ _ S a ha ε t hε ht hℓ
  set a' : Fin (D + 1) := ⟨a, ha⟩ with ha'
  have hform := S.form a' t ht hℓ
  have hu : S.A.Smooth (S.u a' t) := hform.2
  have hΦ : ∀ i, IsPotential S.A (S.rest a t i) := S.rest_isPotential ht hℓ a
  have hth : IsPotential S.A (S.th a') := hform.1.th_pot
  have huP : IsPotential S.A (LocPot.ofFun (S.u a' t)) := isPotential_ofFun S.A _ hu
  have hf : S.A.Smooth fun x => Real.log (secNorm S.L S.s x ^ 2 + ε) :=
    smooth_log_secNorm_sq_add S.L_pot S.s_sec hε
  have hDd : IsPotential S.A (formDiff S.Om.pot (S.th a')) := isPotential_formDiff S.Om.isPot hth
  have hcons := fun (P : LocPot W) (hP : IsPotential S.A P) =>
    forall_cons_of (p := IsPotential S.A) (Φ := S.rest a t) hP hΦ
  have hGi := fun (P : LocPot W) (hP : IsPotential S.A P) =>
    mIntegrable_greenSplit S.L_pot S.s_sec S.s_snc hε _ (hcons P hP)
  have hG := fun Ψ => mInt_greenEp_eq_split (A := S.A) (Φ := Ψ) S.s_sec S.s_snc hε

  have hJ1 : S.J (a + 1) ε t =
      mInt S.A (Fin.cons (S.th a' + LocPot.ofFun (S.u a' t)) (S.rest a t)) (greenSplit S.L S.s ε) := by
    have h := mixedForms_cycle S.Om.pot (S.T t) a ha (a + 1) (Or.inr rfl)
    have h0 : mixedForms S.Om.pot (S.T t) (a + 1) a' = S.th a' + LocPot.ofFun (S.u a' t) := by
      simp [mixedForms, a', UIData.T, curForms, potForm]
    rw [h0] at h
    show mInt S.A (mixedForms S.Om.pot (S.T t) (a + 1)) (greenEp S.L S.s ε) = _
    rw [← mIntSymm S.A (mixedForms S.Om.pot (S.T t) (a + 1)) (Fin.cycleRange a').symm, h, hG]
    rfl
  have hJ0 : S.J a ε t = mInt S.A (Fin.cons S.Om.pot (S.rest a t)) (greenEp S.L S.s ε) := by
    have h := mixedForms_cycle S.Om.pot (S.T t) a ha a (Or.inl rfl)
    have h0 : mixedForms S.Om.pot (S.T t) a a' = S.Om.pot := by simp [mixedForms, a']
    rw [h0] at h
    show mInt S.A (mixedForms S.Om.pot (S.T t) a) (greenEp S.L S.s ε) = _
    rw [← mIntSymm S.A (mixedForms S.Om.pot (S.T t) a) (Fin.cycleRange a').symm, h]
    rfl

  have hOm : mInt S.A (Fin.cons S.Om.pot (S.rest a t)) (greenEp S.L S.s ε) =
      mInt S.A (Fin.cons (S.th a') (S.rest a t)) (greenSplit S.L S.s ε) +
        mInt S.A (Fin.cons (formDiff S.Om.pot (S.th a')) (S.rest a t)) (greenSplit S.L S.s ε) := by
    rw [hG, ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi S.A _
      (Fin.cons (S.th a' + formDiff S.Om.pot (S.th a')) (S.rest a t)) ?_]
    · exact mIntAdd S.A _ _ _ hth hDd hΦ _ (hGi _ hth) (hGi _ hDd)
    · intro i x y
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (add_formDiff_φ _ _ x y).symm
      · simp only [Fin.cons_succ]
  have hpos : 0 ≤ mInt S.A (Fin.cons (formDiff S.Om.pot (S.th a')) (S.rest a t))
      (greenSplit S.L S.s ε) := by
    rw [← hG]
    exact mIntNonneg S.A _ (hcons _ hDd)
      (forall_cons_of (p := IsPsh S.A) (isPsh_formDiff S.Om.isPot hth hform.1.th_le)
        (S.rest_isPsh ht hℓ a)) _ (greenEp_nonneg S.L S.s hε.le)

  have hU : mInt S.A (Fin.cons (LocPot.ofFun (S.u a' t)) (S.rest a t)) (greenSplit S.L S.s ε) =
      mInt S.A (Fin.cons (LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε)) (S.rest a t))
          (S.u a' t) + 2 * mInt S.A (Fin.cons S.L (S.rest a t)) (S.u a' t) -
        2 * S.divInt (S.rest a t) (S.u a' t) := by
    have hlin := mIntLinear S.A _ (hcons _ huP) (-2) (logNormSec S.L S.s)
      (fun x => Real.log (secNorm S.L S.s x ^ 2 + ε))
      (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc _ (hcons _ huP))
      (mIntegrableCont S.A _ (hcons _ huP) _ (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A hf))
    have hpl := poincareLelong S.A S.L S.s S.mult S.comp S.B S.L_pot S.s_sec S.s_snc S.B_holo
      (S.u a' t) hu (S.rest a t) hΦ
    have hbp := byPartsSymm S.A _ (S.u a' t) hf hu (S.rest a t) hΦ
    have hdiv : S.divInt (S.rest a t) (S.u a' t) = ∑ k, (S.mult k : ℝ) * mInt (S.B k)
        (fun i => (S.rest a t i).pullback Subtype.val continuous_subtype_val)
        (S.u a' t ∘ Subtype.val) := rfl
    show mInt S.A _ (fun x => (-2) * logNormSec S.L S.s x + Real.log (secNorm S.L S.s x ^ 2 + ε)) = _
    rw [hlin, hpl, hbp, hdiv]
    ring

  have hpl : S.plTerm a ha ε t =
      2 * mInt S.A (Fin.cons S.L (S.rest a t)) (S.u a' t) +
        mInt S.A (Fin.cons (LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε)) (S.rest a t))
          (S.u a' t) - 2 * S.divInt (S.rest a t) (S.u a' t) := by
    have hcu := ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A hu
    have hL2 : IsPotential S.A (S.L.rsmul 2) := isPotentialRsmul S.A 2 S.L S.L_pot
    have hfP := isPotential_ofFun S.A _ hf
    show mInt S.A (Fin.cons (S.L.rsmul 2 + LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε))
      (S.rest a t)) (S.u a' t) - 2 * S.divInt (S.rest a t) (S.u a' t) = _
    rw [mIntAdd S.A _ _ _ hL2 hfP hΦ _ (mIntegrableCont S.A _ (hcons _ hL2) _ hcu)
      (mIntegrableCont S.A _ (hcons _ hfP) _ hcu), mIntRsmul S.A 2 S.L _ S.L_pot hΦ]
  rw [hJ1, hJ0, hOm, mIntAdd S.A _ _ _ hth huP hΦ _ (hGi _ hth) (hGi _ huP), hU, hpl]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
