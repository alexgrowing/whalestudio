import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaAtReframe

section
variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

noncomputable def reFi : (WO (reS S b) T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.funLeft ℂ ℂ (reWi S T b)

theorem reWi_add (x y : WO S T) : reWi S T b (x + y) = reWi S T b x + reWi S T b y := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_reWi S T b y, ← reW_add, reWi_reW]

theorem reWi_nsmul (k : ℕ) (x : WO S T) : reWi S T b (k • x) = k • reWi S T b x := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_nsmul, reWi_reW]

theorem isHalf_reWi_iff (e : AE D) (x : WO S T) : IsHalf e (reWi S T b x) ↔ IsHalf e x := by
  have h := isHalf_reW_iff S T b e (reWi S T b x)
  rw [reW_reWi] at h
  exact h.symm

theorem reF_reFi (g : WO (reS S b) T → ℂ) : reF S T b (reFi S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reWi_reW]

theorem reFi_reF (g : WO S T → ℂ) : reFi S T b (reF S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reW_reWi]

theorem heisO_reFi (ψ : AddChar (AF D.host.F) ℂ)
    (hB : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (g : WO (reS S b) T → ℂ) :
    reFi S T b (heisO ψ (reS S b) T u g) = heisO ψ S T (reW S T b u) (reFi S T b g) := by
  have h := heisO_reF S T b ψ hB u (reFi S T b g)
  rw [reF_reFi] at h
  rw [h, reFi_reF]

variable (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T))

theorem isSBHalf_comp_reW (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Φ : WO S T → ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ' (fun x => Φ (reW S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reW_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reW_add, reW_nsmul]
    exact h2 _ ((hΛ u).1 hu) ((isHalf_reW_iff S T b e u).2 hh) _
  · intro t ht
    rw [hΛ, reW_nsmul]
    exact h3 _ ht

theorem isSBHalf_comp_reWi (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Ψ : WO (reS S b) T → ℂ)
    (h : IsSBHalf e Λ' Ψ) : IsSBHalf e Λ (fun x => Ψ (reWi S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reWi_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reWi_add, reWi_nsmul]
    exact h2 _ ((hΛ _).2 (by rwa [reW_reWi])) ((isHalf_reWi_iff S T b e u).2 hh) _
  · intro t ht
    have h4 := (hΛ _).1 (h3 _ ht)
    rwa [reW_nsmul, reW_reWi] at h4

theorem reF_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reF S T b (halfInd e Λ) = halfInd e Λ' := by
  funext x
  simp only [reF, LinearMap.funLeft_apply, halfInd, ← hΛ, isHalf_reW_iff]

theorem reFi_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reFi S T b (halfInd e Λ') = halfInd e Λ := by
  rw [← reF_halfInd S T b e Λ Λ' hΛ, reFi_reF]

end

theorem isThetaAt_reframe : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := by
  intro D ψ S T b e Λ Λ' c f₀ Φ f hB hΛ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  refine ⟨⟨(reF S T b) ∘ₗ Tm ∘ₗ reFi S T b, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro Ψ hΨ x hx
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => Ψ (t + x)) =
          fun s => (fun s' => Ψ (reWi S T b s')) (s + reW S T b x) := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, reWi_add, reWi_reW]
      rw [h1, hTm.trans _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b e x).2 hx), ← heisO_reF S T b ψ hB]
      rfl
    · intro Ψ hΨ y hy
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => ψ (symplO (reS S b) T t y) * Ψ t) =
          fun s => ψ (symplO S T s (reW S T b y)) * (fun s' => Ψ (reWi S T b s')) s := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, hB, reW_reWi]
      rw [h1, hTm.modul _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b _ y).2 hy), ← heisO_reF S T b ψ hB]
      rfl
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, map_smul (reFi S T b),
        reFi_halfInd S T b e Λ Λ' hΛ, hTm.vac]
  · intro Tm' hTm'
    let Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := reFi S T b ∘ₗ Tm' ∘ₗ reF S T b
    have hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => Φ (t + x)) =
            fun s => (fun s' => Φ (reW S T b s')) (s + reWi S T b x) := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, reW_add, reW_reWi]
        rw [h1, hTm'.trans _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b e x).2 hx), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · intro Φ hΦ y hy
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => ψ (symplO S T t y) * Φ t) =
            fun s => ψ (symplO (reS S b) T s (reWi S T b y)) * (fun s' => Φ (reW S T b s')) s := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, hB, reW_reWi]
        rw [h1, hTm'.modul _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b _ y).2 hy), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · simp only [Tm, LinearMap.comp_apply]
        rw [map_smul (reF S T b), reF_halfInd S T b e Λ Λ' hΛ, hTm'.vac, reFi_reF]
    rw [hall Tm hPM]
    exact reF_reFi S T b _

end GlobalTheory.ThetaAtReframe
