import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
import Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem surjOn_of_pure (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (hi : Function.Surjective ei)
    (hSB : ∀ v, Set.SurjOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _))
    (hstd : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _) := by
  change schA F κ ≤ (schA F κ).map e
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := Span.exists_sum_finprod hg
  have h1 : pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  obtain ⟨f₀, rfl⟩ := hi f
  have hp : ∀ v, ∃ φ₀ ∈ SB (κ → Fv F v), ev v φ₀ = φ k v ∧ (ev v (φ k v) = φ k v → φ₀ = φ k v) := fun v => by
    by_cases h : ev v (φ k v) = φ k v
    · exact ⟨_, hφSB k v, h, fun _ => rfl⟩
    · obtain ⟨φ₀, h0, h1⟩ := hSB v (hφSB k v)
      exact ⟨φ₀, h0, h1, fun h' => absurd h' h⟩
  choose φ₀ h0 h1 h2 using hp
  have hs : ∀ᶠ v in cofinite, φ₀ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hφstd k, hstd] with v e1 e2
    rw [h2 v (by rw [e1, e2]), e1]
  refine ⟨_, GlobalTheory.TensUniq.pure_mem_schA f₀ φ₀ h0 hs, ?_⟩
  rw [hloc f₀ φ₀ h0 hs]
  simp only [h1]

theorem exists_ne_of_surjOn {e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)} (h : Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _)) :
    ∃ Φ ∈ schA F κ, e Φ ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  obtain ⟨Φ, hΦ, rfl⟩ := h hφ
  exact ⟨Φ, hΦ, fun h1 => h0 (by rw [h1]; rfl)⟩

theorem tw_surj (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} (d d₁ : Darboux B κ) : ∃ e, Tw ψ d d₁ e ∧ Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _) := by
  obtain ⟨e, ei, ev, h1, h2, h3, -, h5, h6⟩ := hA F ψ hψ κ (d.e.symm.trans d₁.e) fun w w' => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← d₁.form, d.form, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hs := surjOn_of_pure e ei ev ei.surjective (fun v => (h3 v).surjOn) h5 h6
  refine ⟨e, ⟨h1, fun u Φ hΦ => ?_, Span.comp_mem_adm e ei ev (fun v φ hφ => (h3 v).mapsTo hφ) h5 h6, exists_ne_of_surjOn hs⟩, hs⟩
  have := h2 (d.e u) Φ hΦ
  rwa [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this

theorem twEx (hA : PositivityTheory.Mix.AdelSt) : TwEx := fun _ _ _ _ hψ _ _ _ _ _ _ d d₁ => (tw_surj hA hψ d d₁).imp fun _ h => h.1

theorem tw_bij (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} (d d₁ : Darboux B κ) : ∃ e e', Tw ψ d d₁ e ∧ Tw ψ d₁ d e' ∧
      Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) ∧ (∀ Φ ∈ schA F κ, e' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e' Φ) = Φ := by
  obtain ⟨e, h, hs⟩ := tw_surj hA hψ d d₁
  obtain ⟨e', h', -⟩ := tw_surj hA hψ d₁ d
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h'.ne
    obtain ⟨Ψ, hΨ, rfl⟩ := hs hΦ
    exact hne ((ha Ψ hΨ).trans (by rw [a0, zero_smul]))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  refine ⟨e, _, h, h'.smul (inv_ne_zero a0), ⟨h.maps, fun x hx y hy hxy => ?_, hs⟩, h1, fun Φ hΦ => ?_⟩
  · rw [← h1 x hx, hxy, h1 y hy]
  · obtain ⟨Ψ, hΨ, rfl⟩ := hs hΦ
    rw [h1 Ψ hΨ]

end PositivityTheory.ThKF0

end
