import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable local instance measFvEvLoc {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvEvLoc {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

noncomputable section

namespace GlobalTheory.EvLocIntertwine

open Classical in

theorem ev_locOp_comm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (ψ : AddChar (AF F) ℂ) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    M.IsGood ψ → M₁.IsGood ψ → IsLocPart M M₁ e ei ev →
    ∀ (v : Pl F) (T : Fn F n d → Fn F n d) (T₁ : Fn F n₁ d₁ → Fn F n₁ d₁),
      (∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ' ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) T φ φ') →
      (∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∃ φ' ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Acts (evFin F v) T₁ φ φ') →
      (∀ Φ ∈ schA F (Fin n × Fin d), e (T Φ) = T₁ (e Φ)) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (locOp v T φ) = locOp v T₁ (ev v φ) := by
  intro F E _ _ _ _ _ σ ψ n d n₁ d₁ X W X₁ W₁ M M₁ e ei ev hM hM₁ hL v T T₁ hT hT₁ he φ hφ
  obtain ⟨hei, hev, hloc⟩ := hL
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std
  obtain ⟨r₁, hr₁, hr₁t⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) M₁.vac hM₁.std
  have hr₁0 : r₁ ≠ 0 := by
    have ht : tens (evFin F v) (fun _ => (1 : ℂ)) r₁ = r₁ := by
      funext x
      simp [tens]
    have h1 := hr₁t (fun _ => 1)
    rw [ht] at h1
    rw [h1]
    refine GlobalTheory.EvNonzero.pure_ne_zero (ei f) hf _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v _ hM₁.std)
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      intro h
      exact one_ne_zero (congrFun h 0)
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).2.1
  have hupd : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update M.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM.vac w).1
  have hupd₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ w, Function.update M₁.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).1
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ r₀ := fun φ hφ =>
    ⟨hr₀, by
      rw [hr₀t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM.std)⟩
  have hRest₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Rest (evFin F v) φ r₁ := fun φ hφ =>
    ⟨hr₁, by
      rw [hr₁t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (hupd₁ φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM₁.std)⟩
  have hevSB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB _ := by
    intro φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hev_pure : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), e (tens (evFin F v) φ r₀) = tens (evFin F v) (ev v φ) r₁ := by
    intro φ hφ
    have hc : ∀ᶠ w in cofinite, Function.update M.vac v φ w = M.vac w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
    have hfun : (fun w => ev w (Function.update M.vac v φ w)) = Function.update M₁.vac v (ev v φ) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hw, (hev w).1]
    rw [hr₀t φ, hloc f _ (hupd φ hφ) hc, hfun, hr₁t]
  obtain ⟨φ', hφ', hA⟩ := hT φ hφ
  have hA' := acts_locOp (T := T) ⟨φ', hφ', hA⟩
  obtain ⟨φ₁', hφ₁', hA₁⟩ := hT₁ _ (hevSB φ hφ)
  have hA₁' := acts_locOp (T := T₁) ⟨φ₁', hφ₁', hA₁⟩
  apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v r₁ hr₁ hr₁0
  rw [← hev_pure _ (locOp_mem v T φ), ← hA' r₀ (hRest φ hφ), he _ (hRest φ hφ).2, hev_pure φ hφ,
    hA₁' r₁ (hRest₁ _ (hevSB φ hφ))]

end GlobalTheory.EvLocIntertwine

end
