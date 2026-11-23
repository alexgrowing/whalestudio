import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.EvOnto

open scoped Classical in

theorem ev_surjOn_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  intro F _ _ κ _ e ei ev hSBev hfix he hsurj hne v χ hχ
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let Φ₁ : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => ev w (stdInd F κ w)
  have hstdSB : ∀ w : Pl F, stdInd F κ w ∈ SB (κ → Fv F w) := fun w => GlobalTheory.StdVacuum.indicator_mem_SB w
  have hΦstd : ∀ᶠ w in cofinite, Φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := hfix
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) ∈ schA F κ := by
    refine GlobalTheory.TensUniq.pure_mem_schA f₀ _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually Φ₁ v χ hΦstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hSBev w _ (hstdSB w)
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj hmem
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ w in cofinite, φ i w = stdInd F κ w := by
    intro i
    filter_upwards [T.eventually_cofinite_notMem] with w hT
    exact hstd i w hT
  have hvac' : ∀ i, ∀ᶠ w in cofinite, (fun w => ev w (φ i w)) w =
      Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hvac i, hfix] with w h1 h2
    rw [h1]; exact h2
  have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f₀ Φ₁ hΦstd
  choose r hr hrt using fun i => GlobalTheory.PureFactor.exists_rest_factor v (ei (f i)) (fun w => ev w (φ i w)) (hvac' i)
  have hrt' : ∀ i, tens (evFin F v) (ev v (φ i v)) (r i) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    intro i
    rw [hrt i]
    congr 1
    exact Function.update_eq_self v (fun w => ev w (φ i w))
  have hex : ∃ x₀, r₀ x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v fun _ => 1) = 0 := by
      rw [← hr₀t]
      funext x
      simp [tens, hc]
    have hf : f₀ = 0 := by
      refine GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ _ (fun w => ?_)
        (GlobalTheory.PureFactor.update_eventually Φ₁ v _ hΦstd) h0
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        intro h
        exact one_ne_zero (congrFun h 0)
      · rw [Function.update_of_ne hw]; exact hne w
    exact hf₀ (by rw [hf]; rfl)
  obtain ⟨x₀, hx₀⟩ := hex
  refine ⟨∑ i, (r i x₀ / r₀ x₀) • φ i v, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hSB i v), ?_⟩
  funext y
  let z : κ → AF F := fun j => GlobalTheory.LatVac.liftV v (y j - evFin F v (x₀ j))
  have hz : At (evFin F v) z := by
    intro u hu
    funext j
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun j => evFin F v ((x₀ + z) j)) = y := by
    funext j
    rw [Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV]
    ring
  have key : χ y * r₀ x₀ = ∑ i, ev v (φ i v) y * r i x₀ := by
    have h := congrFun hid (x₀ + z)
    rw [← hr₀t, Finset.sum_apply] at h
    simp only [← hrt', tens, hev, hr₀ x₀ z hz] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [hr i x₀ z hz]
  rw [map_sum, Finset.sum_apply]
  apply mul_right_cancel₀ hx₀
  rw [key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.EvOnto
