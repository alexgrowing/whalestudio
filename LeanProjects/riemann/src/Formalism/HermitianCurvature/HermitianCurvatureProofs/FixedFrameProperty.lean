import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

theorem fixed_frame_property : C2.FixFrame := by
  intro k r z hz
  ext g
  constructor
  · rintro ⟨hgV, hfix⟩
    have hS : g ∈ Sset k r z := by
      rw [← standard_flag_property k r z hz]
      exact ⟨hgV, fun a => by simp [hfix a]⟩
    refine ⟨hS, uMap_eq hz g 1 fun b => ?_⟩
    simp [Matrix.one_apply, hfix b]
  · rintro ⟨hS, hU⟩
    have hS' := hS
    rw [← standard_flag_property k r z hz] at hS'
    refine ⟨hS'.1, fun a => ?_⟩
    rw [((unipotent_map_frame k r z hz).1 g hS).1 a, hU]
    simp [Matrix.one_apply]

theorem fibre_stabilizer : C2.FibreStab := by
  intro k r z z' hstd g hg _
  have hHdet : IsUnit (Hpk k r).det :=
    Matrix.isUnit_det_of_right_inverse (majorant_estimate k r).2.1
  obtain ⟨_, hmul, hinv⟩ := uHGroup _ (Hpk k r) hHdet
  have hgu : IsUnit g.det := (hinv g hg).1
  have hFz := fixed_frame_property k r z hstd.2.1
  have hFz' := fixed_frame_property k r z' hstd.2.2
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, hpq⟩
    rw [← hFz] at hp
    have hpu : IsUnit p.det := (hinv p hp.1).1
    have h1 : g * q = p * g := by
      calc g * q = p * (p⁻¹ * g * q) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hpu, Matrix.one_mul]
        _ = p * g := by rw [hpq]
    have hq_eq : g⁻¹ * p * g = q := by
      calc g⁻¹ * p * g = g⁻¹ * (g * q) := by rw [h1, Matrix.mul_assoc]
        _ = q := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul]
    refine ⟨p, ⟨hp.1, ?_⟩, rfl, hq_eq⟩
    rintro (a | b)
    · exact hp.2 a
    · rw [← hFz'] at hq
      show p *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b
      rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, hq.2 b]
  · rintro ⟨h, ⟨hhV, hhfix⟩, rfl, rfl⟩
    have hhu : IsUnit h.det := (hinv h hhV).1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hFz]
      exact ⟨hhV, fun a => hhfix (Sum.inl a)⟩
    · rw [← hFz']
      refine ⟨hmul _ (hmul _ (hinv g hg).2 h hhV) g hg, fun b => ?_⟩
      have hb : h *ᵥ (g *ᵥ fvec k r z' b) = g *ᵥ fvec k r z' b := hhfix (Sum.inr b)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hgu, Matrix.one_mulVec]
    · calc h⁻¹ * g * (g⁻¹ * h * g) = h⁻¹ * (g * g⁻¹) * h * g := by simp only [Matrix.mul_assoc]
        _ = g := by
          rw [Matrix.mul_nonsing_inv _ hgu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul]

end Formalism.FourierDecayAlt.P
