import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseGraph
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VeroneseGraphImage.proof : VeroneseGraphImage.Statement := by
  intro D

  let f₀ : MRing (GlobalTheory (Fin (D + 1))) →+* Veronese.Fld D :=
    (Veronese.polyMap D).comp
      (rename (fun p : Σ _ : Unit, Fin (D + 1) => p.2) : MvPolynomial _ ℤ →ₐ[ℤ] _).toRingHom
  have hf₀ : Function.Injective f₀ := by
    refine (Veronese.polyMap_injective D).comp (rename_injective _ ?_)
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  have hf₀X : ∀ i, f₀ (X ⟨(), i⟩) = Veronese.t D i := by
    intro i
    simp [f₀, Veronese.polyMap, Veronese.t]
  let P : Ideal (MRing (GlobalTheory (Fin (D + 1)))) := ⊥
  let φ : MRing (GlobalTheory (Fin (D + 1))) ⧸ P →+* Veronese.Fld D :=
    Ideal.Quotient.lift P f₀ fun a ha => by
      rw [Ideal.mem_bot] at ha
      simp [ha]
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a = 0 := hf₀ (by rw [map_zero]; exact (Ideal.Quotient.lift_mk _ _ _).symm.trans ha)
    rw [this, map_zero]

  let ψ : Polynomial (Veronese.Fld D) →+* MvPolynomial Unit (Veronese.Fld D) :=
    Polynomial.eval₂RingHom C (X ())
  let ev : MvPolynomial Unit (Veronese.Fld D) →+* Polynomial (Veronese.Fld D) :=
    eval₂Hom Polynomial.C fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p
  let G : MRing (GlobalTheory (Veronese.Idx D)) →+* MvPolynomial Unit (Veronese.Fld D) :=
    (MvPolynomial.map φ).comp ((graphMap P (Veronese.forms D)).comp
      (rename (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) :
        MRing (GlobalTheory (Veronese.Idx D)) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ (Veronese.x D) f) := by
    have h : G = ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun
          (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom).comp C)) n
      · rintro ⟨u, q⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          rename_X]
        rw [show (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)) ⟨(), q⟩) = ⟨Sum.inr (), q⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk P (Veronese.forms D ⟨(), q⟩)) = Veronese.x D ⟨(), q⟩ from by
          rw [Ideal.Quotient.lift_mk]
          simp only [Veronese.forms, map_mul, hf₀X, Veronese.x]]
        simp [ψ]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap P (Veronese.forms D)) ↔
    f ∈ RingHom.ker (coneMap ℤ (Veronese.x D))
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap P (Veronese.forms D) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ (Veronese.x D) f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
