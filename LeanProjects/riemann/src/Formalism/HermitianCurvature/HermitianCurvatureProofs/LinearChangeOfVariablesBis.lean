import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

namespace C2x7

variable {k r : ℕ}

lemma one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun a => ⟨by simp, by simp⟩, by simp⟩

lemma N_sub_S {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, one_mem_UW z, n, hn, by simp⟩

lemma UW_sub_S {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩

lemma fix_inv {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ C2.FixSet k r z) :
    g⁻¹ ∈ C2.FixSet k r z := by
  have hu : IsUnit g.det := WeylGroupFacts.isUnit_of_uh hg.1
  refine ⟨WeylGroupFacts.uh_inv hg.1, fun a => ?_⟩
  calc g⁻¹ *ᵥ fvec k r z a = g⁻¹ *ᵥ (g *ᵥ fvec k r z a) := by rw [hg.2 a]
    _ = fvec k r z a := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

end C2x7

open C2x5 C2x6 C2x7

theorem zhat_section_of_parts : C2.ZhatSectionOfParts := by
  intro hZE hUM hTM _ k r z z' γ hstd n0 hn0 v hv h hh s' hs'
  have hz := hstd.2.1
  have hz' := hstd.2.2
  obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
  have hSg := symmetric_group_holds k r z hz.1
  have hn0S : n0 ∈ Sset k r z := N_sub_S hn0.1
  have hτS : C2.tauM k r z v ∈ Sset k r z := N_sub_S hτN
  have hhS : h ∈ Sset k r z := UW_sub_S hh
  have hs1 : n0 * C2.tauM k r z v ∈ Sset k r z := hSg.2.1 _ hn0S _ hτS
  have hs : n0 * C2.tauM k r z v * h ∈ Sset k r z := hSg.2.1 _ hs1 _ hhS
  have hU := hUM k r z hz
  have hu : C2.uMap k r z (n0 * C2.tauM k r z v * h) = v := by
    rw [(hU.1 _ hs1).2.2 h hhS, (hU.1 _ hn0S).2.2 _ hτS, hn0.2, hτu, hU.2 h hh, Matrix.one_mul,
      Matrix.mul_one]
  rw [hZE k r z z' hz hz' _ hs s' hs' γ, hu]

theorem fibreOrbitOfParts_statement : C2.FibreOrbitOfParts := by
  intro hW hFF hGB hC1 k r z z' hstd g₁ hg₁ g₂ hg₂ hG hZ
  have hG2 : 0 < Gf k r z z' g₂ := by
    have : Gf k r z z' g₂ = Gf k r z z' g₁ := by unfold Gf Dmin; rw [hZ]
    rw [this]; exact hG
  have hli1 := (hC1 k r z z' g₁ hstd ⟨hg₁, hG⟩).1
  have hli2 := (hC1 k r z z' g₂ hstd ⟨hg₂, hG2⟩).1
  have hgram : ∀ i j, herm (Hpk k r) (gramVec k r z z' g₁ i) (gramVec k r z z' g₁ j) =
      herm (Hpk k r) (gramVec k r z z' g₂ i) (gramVec k r z z' g₂ j) := by
    intro i j
    have e : gramM k r z z' g₁ = gramM k r z z' g₂ := by
      rw [hGB k r z z' hstd.2.1 hstd.2.2 g₁ hg₁, hGB k r z z' hstd.2.1 hstd.2.2 g₂ hg₂, hZ]
    exact congrFun (congrFun e j) i
  obtain ⟨s0, hs0, hs0x⟩ := hW k r _ (gramVec k r z z' g₁) (gramVec k r z z' g₂) hli1 hli2 hgram
  have hs0F : s0 ∈ C2.FixSet k r z := ⟨hs0, fun a => hs0x (Sum.inl a)⟩
  have hu0 : IsUnit s0.det := WeylGroupFacts.isUnit_of_uh hs0
  have hu1 : IsUnit g₁.det := WeylGroupFacts.isUnit_of_uh hg₁
  have hu2 : IsUnit g₂.det := WeylGroupFacts.isUnit_of_uh hg₂
  set t := g₂⁻¹ * s0 * g₁ with ht
  have htF : t ∈ C2.FixSet k r z' := by
    refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hg₂) hs0) hg₁, fun b => ?_⟩
    have := hs0x (Sum.inr b)
    simp only [gramVec] at this
    rw [ht, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu2, Matrix.one_mulVec]
  have hut : IsUnit t.det := WeylGroupFacts.isUnit_of_uh htF.1
  refine ⟨s0⁻¹, ?_, t⁻¹, ?_, ?_⟩
  · rw [← hFF k r z hstd.2.1]; exact fix_inv hs0F
  · rw [← hFF k r z' hstd.2.2]; exact fix_inv htF
  · rw [Matrix.nonsing_inv_nonsing_inv _ hu0]
    have e : g₂ * t = s0 * g₁ := by
      rw [ht, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
    calc g₂ = g₂ * t * t⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut, Matrix.mul_one]
      _ = s0 * g₁ * t⁻¹ := by rw [e]

theorem linear_change_of_variables_bis : C2.LinCOV := by
  intro a φ ha
  have hpos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  set f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ a).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq a := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply]
  have hne : LinearMap.det f ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ)) hne
  have hcoe : (⇑f : ℂ → ℂ) = ⇑(MeasurableEquiv.mulLeft₀ a ha) := by ext c; rfl
  calc ∫⁻ c : ℂ, φ (a * c) = ∫⁻ c : ℂ, φ (MeasurableEquiv.mulLeft₀ a ha c) := rfl
    _ = ∫⁻ D, φ D ∂(Measure.map (MeasurableEquiv.mulLeft₀ a ha) volume) := (lintegral_map_equiv φ _).symm
    _ = ∫⁻ D, φ D ∂(Measure.map f volume) := by rw [hcoe]
    _ = ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) * ∫⁻ D : ℂ, φ D := by
        rw [hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), Complex.normSq_eq_norm_sq]
        rfl

end Formalism.FourierDecayAlt.P
