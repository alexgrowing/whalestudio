import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairExtensionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixUXScalar

theorem evalZero_scalar_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      (∀ g : UA σ X.J, ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • om₁ (g, 1) (e Φ)) →
      ∀ g : UA σ X.J, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = om₁ (g, 1) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he hc
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e
    hP.good hP₁.good he
  have hpres : ∀ g, ∀ Φ ∈ schA F (Fin n × Fin d), om (g, 1) Φ ∈ schA F (Fin n × Fin d) := fun g Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres (g, 1) Φ hΦ

  have hinj : ∀ (g : UA σ X.J) (f : Fn F n d₁), om₁ (g, 1) f = 0 → f = 0 := by
    intro g f hf
    have h1 : om₁ (g⁻¹, 1) (om₁ (g, 1) f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, ← Prod.one_eq_mk, map_one,
        Module.End.one_apply]
    rw [← h1, hf, map_zero]
  choose c hc' using hc

  have huniq : ∀ (g : UA σ X.J) (a b : ℂ), a • om₁ (g, 1) (e Φ₀) = b • om₁ (g, 1) (e Φ₀) → a = b := by
    intro g a b hab
    have h2 : (a - b) • om₁ (g, 1) (e Φ₀) = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (hinj g _ h) hne
  have hone : c 1 = 1 := by
    apply huniq 1
    rw [← hc' 1 Φ₀ hΦ₀, one_smul, ← Prod.one_eq_mk, ← Prod.one_eq_mk, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply]
  have hmul : ∀ g h, c (g * h) = c g * c h := by
    intro g h
    apply huniq (g * h)
    have e1 : om (g * h, 1) Φ₀ = om (g, 1) (om (h, 1) Φ₀) := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    have e2 : om₁ (g * h, 1) (e Φ₀) = om₁ (g, 1) (om₁ (h, 1) (e Φ₀)) := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    rw [← hc' (g * h) Φ₀ hΦ₀, e1, hc' g _ (hpres h Φ₀ hΦ₀), hc' h Φ₀ hΦ₀, map_smul, smul_smul, e2]
  let c₀ : UA σ X.J →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  let cu : UA σ X.J →* ℂˣ := c₀.toHomUnits
  have hcu : cu = 1 := GlobalTheory.T.skew_adapted_plane_pair_extension hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he cu
    (fun g Φ hΦ => hc' g Φ hΦ)
  intro g Φ hΦ
  have hg : c g = 1 := by
    have := congrArg (fun u : UA σ X.J →* ℂˣ => ((u g : ℂˣ) : ℂ)) hcu
    simpa [cu, c₀] using this
  rw [hc' g Φ hΦ, hg, one_smul]

end GlobalTheory.MixUXScalar
