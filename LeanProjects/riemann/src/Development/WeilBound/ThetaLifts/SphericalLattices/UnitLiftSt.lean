import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas

theorem unitLiftSt : UnitLiftSt := by
  intro F E _ _ _ _ _ v y
  have hab : ∀ a b : Ev E v, sgE E v a * sgE E v b = sgE E v (a * b) := fun a b => by
    have e := GlobalTheory.EmbChart.tensAt_mul_right (E := E) v a (sgE E v b)
    rw [comp_sgE] at e
    exact e
  have key : ∀ a b : Ev E v, (1 + sgE E v a) * (1 + sgE E v b) = 1 + sgE E v ((1 + a) * (1 + b) - 1) := fun a b => by
    have e : (1 + a) * (1 + b) - 1 = a + b + a * b := by ring
    rw [e, map_add, map_add, ← hab]
    ring
  refine ⟨⟨1 + sgE E v ((y : Ev E v) - 1), 1 + sgE E v (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1), ?_, ?_⟩, ?_, ?_⟩
  · rw [key, show (1 : Ev E v) + ((y : Ev E v) - 1) = y by ring, show (1 : Ev E v) + (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1) = _ by ring,
      Units.mul_inv, sub_self, map_zero, add_zero]
  · rw [key, show (1 : Ev E v) + ((y : Ev E v) - 1) = y by ring, show (1 : Ev E v) + (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1) = _ by ring,
      Units.inv_mul, sub_self, map_zero, add_zero]
  · change At (evFin F v) (1 + sgE E v _ - 1)
    rw [add_sub_cancel_left]
    exact at_sgE _
  · change compFin F E v (1 + sgE E v _) = _
    rw [map_add, map_one, comp_sgE]
    ring

theorem pInvSt : PInvSt := by
  intro F E _ _ _ _ _ σ d W v w hw m Cy hL p hp
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨hpU, t₀, ht₀⟩ := hp
  set φ := piE (F := F) (E := E) h with hφ
  have hpinv : (mat p⁻¹).map φ * (mat p).map φ = 1 := by
    rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

  have hfree : ∀ s : Fin m → w.adicCompletion E, Cy.map φ *ᵥ s = 0 → s = 0 := fun s hs => by
    obtain ⟨s', hs', e⟩ := vec_surj h s
    have h0 : Cy *ᵥ s' = 0 := vec_inj hw h (by rw [sub_zero]; exact at_mulVec_left hL.supp _) (by
      rw [piE_mulVec, e, hs]; funext i; simp)
    rw [← e, hL.free s' hs' h0]; funext i; simp
  have hdet : ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → (t.map φ).det ≠ 0 := fun t ht hdt => by
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdt
    refine hs0 (hfree s ?_)
    have e1 : (mat p).map φ * Cy.map φ = Cy.map φ * t.map φ := by rw [← Matrix.map_mul, ht, Matrix.map_mul]
    have e2 : Cy.map φ *ᵥ s = (mat p⁻¹).map φ *ᵥ ((Cy.map φ * t.map φ) *ᵥ s) := by
      rw [← e1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hpinv, Matrix.one_mul]
    rw [e2, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hunit : ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → IsUnit (t.map (compFin F E v)).det := fun t ht => by
    have e : (t.map (compFin F E v)).map (toCompl h) = t.map φ := by rw [Matrix.map_map]; rfl
    have hne : toCompl h (t.map (compFin F E v)).det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, e]; exact hdet t ht
    exact (MulEquiv.isUnit_map (RingEquiv.ofBijective (toCompl h) (toCompl_bijective hw h)).toMulEquiv).1
      (isUnit_iff_ne_zero.2 hne)
  refine ⟨⟨inv_mem_UAt hpU, ?_⟩, hunit⟩
  have hu : IsUnit (t₀.map φ).det := isUnit_iff_ne_zero.2 (hdet t₀ ht₀)
  obtain ⟨t', ht'a, ht'⟩ := mat_surj h (t₀.map φ)⁻¹
  refine ⟨t', mat_inj hw h (at_sub (at_mul_right _ hL.supp) (at_mul_left hL.supp _)) ?_⟩
  have e1 : (mat p).map φ * Cy.map φ = Cy.map φ * t₀.map φ := by rw [← Matrix.map_mul, ht₀, Matrix.map_mul]
  rw [Matrix.map_mul, Matrix.map_mul, ht']
  calc (mat p⁻¹).map φ * Cy.map φ = (mat p⁻¹).map φ * (Cy.map φ * (t₀.map φ * (t₀.map φ)⁻¹)) := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Cy.map φ * (t₀.map φ)⁻¹ := by
        rw [← Matrix.mul_assoc (Cy.map φ), ← e1, Matrix.mul_assoc, ← Matrix.mul_assoc ((mat p⁻¹).map φ), hpinv, Matrix.one_mul]

end PositivityTheory.Sph

end
