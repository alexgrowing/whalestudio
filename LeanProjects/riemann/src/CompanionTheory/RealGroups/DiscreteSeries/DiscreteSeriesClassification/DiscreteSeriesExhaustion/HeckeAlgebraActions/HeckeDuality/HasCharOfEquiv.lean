import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.GlRelTau
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsExtraMore

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)

variable {n : ℕ}

theorem omD_eq_om_tau (X : GMod n) : omD X = om (tauMod X) := by
  refine LinearMap.ext fun f => funext fun a => ?_
  simp [omD, om_apply, tauMod, ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.eeVd, LinearMap.pi_apply, Finset.sum_neg_distrib]

theorem backSub_eq (X : GMod n) (z : ℂ) : backSub X z = stepSub (tauMod X) (-z) := by
  unfold backSub stepSub
  rw [omD_eq_om_tau]
  congr 1

theorem capelliPoly_neg (χ : Fin n → ℂ) (Y : ℂ) :
    Formalism.QuantumDeterminants.capP (-χ) Y = (-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ (-Y) := by
  unfold Formalism.QuantumDeterminants.capP
  have h1 : ((-1 : ℂ) ^ n) = ∏ _s : Fin n, (-1 : ℂ) := by simp [Finset.prod_const, Finset.card_univ]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Pi.neg_apply]
  ring

theorem hasChar_tau (hT : QdetTau) {X : GMod n} {χ : Fin n → ℂ} (h : HasChar X χ) :
    HasChar (tauMod X) (-χ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  have e1 : -(Y + ((n : ℂ) - 1) / 2) + ((n : ℂ) - 1) = -Y + ((n : ℂ) - 1) / 2 := by ring
  have hT' : qdet (fun a b => -X.E b a) (Y + ((n : ℂ) - 1) / 2) =
      ((-1 : ℂ) ^ n) • qdet X.E (-(Y + ((n : ℂ) - 1) / 2) + ((n : ℂ) - 1)) := hT n X _
  have e2 : qdet (fun a b => -X.E b a) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V) =
      ((-1 : ℂ) ^ n) • (qdet X.E (-Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ (-Y) • (1 : Module.End ℂ X.V)) := by
    rw [hT', e1, capelliPoly_neg, smul_sub, smul_smul]
  change (qdet (fun a b => -X.E b a) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V)) ^ k = 0
  rw [e2, smul_pow, hk (-Y), smul_zero]

theorem hasChar_of_equiv {Y₁ Y₂ : GMod n} (e : Y₁.V ≃ₗ[ℂ] Y₂.V) (he : ∀ a b x, e (Y₁.E a b x) = Y₂.E a b (e x))
    {μ : Fin n → ℂ} (h : HasChar Y₂ μ) : HasChar Y₁ μ := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  let φ : Module.End ℂ Y₁.V ≃ₐ[ℂ] Module.End ℂ Y₂.V := e.conjAlgEquiv ℂ
  have hφ : ∀ f : Module.End ℂ Y₁.V, φ.toAlgHom f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap := fun f =>
    LinearEquiv.conjAlgEquiv_apply e f
  have hφE : (fun a b => φ.toAlgHom (Y₁.E a b)) = Y₂.E := by
    funext a b
    refine LinearMap.ext fun y => ?_
    rw [hφ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [he, LinearEquiv.apply_symm_apply]
  have hq := (GlobalTheory.CompanionTheory.CapelliMap.map_qdet_etr (Module.End ℂ Y₁.V) (Module.End ℂ Y₂.V) φ.toAlgHom n Y₁.E
    (Y + ((n : ℂ) - 1) / 2) 0).1
  rw [hφE] at hq
  apply φ.injective
  have h0 := hk Y
  rw [← hq] at h0
  rw [map_zero, ← h0]
  change φ.toAlgHom _ = _
  rw [map_pow, map_sub, map_smul, map_one]

theorem dualfacts_of (hT : QdetTau) (hC : CayleyHam) (hS : StepChar) (hN : NonVan) : DualFacts := by
  intro n X χ h
  have hτ := hasChar_tau hT h
  refine ⟨?_, fun s hB => ?_, fun s hnt hfree => ?_⟩
  · obtain ⟨K, hK⟩ := hC n (tauMod X) (-χ) hτ
    refine ⟨K, ?_⟩
    rw [omD_eq_om_tau]
    simp only [Pi.neg_apply] at hK
    exact hK
  · have hY := hS n (tauMod X) (-χ) s hτ
    have hY' := hasChar_tau hT hY
    have e3 : -((-χ) + Pi.single s 1) = χ - Pi.single s 1 := by rw [neg_add, neg_neg, sub_eq_add_neg]
    rw [e3] at hY'
    refine hasChar_of_equiv (Y₂ := tauMod (step (tauMod X) ((-χ) s)))
      (LinearEquiv.ofEq _ _ (backSub_eq X (χ s))) (fun a b x => ?_) hY'
    obtain ⟨y, hy⟩ := x
    apply Subtype.ext
    funext d
    change X.E a b (y d) - ((if d = b then (LinearMap.proj a : (Fin n → X.V) →ₗ[ℂ] X.V) else 0) y) =
      -((-X.E a b) (y d) + (if d = b then y a else 0))
    by_cases h : d = b
    · simp [h]; abel
    · simp [h]
      rfl
  · have := hN n (tauMod X) (-χ) s hτ hnt (fun r hr => hfree r (by simp only [Pi.neg_apply] at hr; linear_combination -hr))
    rw [backSub_eq]
    exact this

end CompanionTheory.RgExh.Hk
