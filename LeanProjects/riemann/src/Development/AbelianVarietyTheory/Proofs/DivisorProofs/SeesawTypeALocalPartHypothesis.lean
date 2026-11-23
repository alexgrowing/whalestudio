import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationIsoBTriplePair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VanishLocInvA

open scoped Classical

theorem inv_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {b a' : ℕ}
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)), u ∈ isoA H H' → At (evFin F v) u →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ) = ev v φ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' e hEv ei ev hloc X om om' om₁ om₁' hT hT₁ v u hu hat φ hφ
  obtain ⟨hei, hev, hfac⟩ := hloc
  set φ₁ := schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ with hφ₁def
  have hφ₁ : φ₁ ∈ SB _ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hei (ContinuousLinearMap.ext hc)
  have hSB : ∀ c ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∀ w, Function.update G.M.vac v c w ∈ SB _ := by
    intro c hc w
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self]; exact hc
    · rw [Function.update_of_ne hwv]; exact (hT.geo.hM.vac w).1
  have hco : ∀ c : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ,
      ∀ᶠ w in cofinite, Function.update G.M.vac v c w = G.M.vac w := by
    intro c
    filter_upwards [Filter.eventually_cofinite_ne v] with w hw
    exact Function.update_of_ne hw _ _
  have hstd := GlobalTheory.PureFactor.update_eventually G.M.vac v φ hT.geo.hM.std
  have hpure := GlobalTheory.TensUniq.pure_mem_schA f _ (hSB φ hφ) hstd
  have hfin := GlobalTheory.PureFactor.mulSupport_finite _ hstd
  have hact : Acts (evFin F v) (G.M.co.rho B.ψ u) (Function.update G.M.vac v φ v) φ₁ := by
    rw [Function.update_self]
    exact GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hat φ
  have hrho := GlobalTheory.ThK.LocalOps.acts_pure v (G.M.co.rho B.ψ u) f _ φ₁ hpure hfin hact
  rw [Function.update_idem] at hrho
  have hinv := hEv.inv u hu _ hpure
  rw [hrho, hfac f _ (hSB φ₁ hφ₁) (hco φ₁), hfac f _ (hSB φ hφ) (hco φ)] at hinv
  have hup : ∀ c : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ,
      (fun w => ev w (Function.update G.M.vac v c w)) = Function.update G₁.M.vac v (ev v c) := by
    intro c
    funext w
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]; exact (hev w).1
  rw [hup, hup] at hinv
  exact GlobalTheory.VanishLocInv.eq_of_pure_update_eq G₁.M.vac (fun w => (hT₁.geo.hM.vac w).2.1) hT₁.geo.hM.std (ei f) hf v _ _ hinv

end GlobalTheory.VanishLocInvA
