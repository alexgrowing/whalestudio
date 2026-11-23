import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.PBJ

section lev0

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem ptG_one (TT : ℝ) (ζ : ℂ) : D.ptG TT 0 [(1, ζ)] = Complex.normSq ζ - TT := by
  simp [D.ptG, D.ptMatN, D.ptEntry, Matrix.det_fin_one]

theorem isLocPt_one {ζ : ℂ} (hζ : ζ ≠ 0) : D.IsLocPt [(1, ζ)] (0 + 1) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ⟨le_refl _, hζ⟩
  · simp [D.ptSize]

theorem orbJ_one_eq (S : B.RealPlaceData k ρ Wp Wq) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ)
    (hpos : 0 < Gf k ρ S.z S.z' γ) {d : Fin (ρ + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k ρ S.z S.z' γ = C2.monoP 1 d) (F : B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    D.orbJ S γ (D.muR S γ 1) F = B.JF S F γ := by
  have : IsEmpty (C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1)))) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id] at h2
    exact absurd h1 (not_lt.2 h2.le)⟩
  have hone : D.rhoOfU S γ 1 = 1 := by
    unfold D.rhoOfU
    split_ifs with hex
    · have h1mem : (1 : B.Mat k ρ) ∈ C6.Rset γ := by
        refine ⟨WeylGroupFacts.mem_n_one, ?_⟩
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ)]
        exact WeylGroupFacts.mem_n_one
      exact Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZ hex.choose_spec.1 h1mem
        (hex.choose_spec.2.trans (Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one S.z ⟨S.z_mem, S.T_pos⟩).symm)
    · rfl
  have hlow : C2.lowOf (fun q : C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1))) => q.1) isEmptyElim = 1 := by
    unfold C2.lowOf
    ext i j
    simp
  have hR : D.muR S γ 1 = Measure.dirac (Matrix.of.symm (1 : B.Mat k ρ)) := by
    unfold D.muR
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty _ isEmptyElim, Measure.map_dirac' Subsingleton.measurable,
      hlow, Matrix.conjTranspose_one, hone]
  have hact : ∀ p, C6.actR γ 1 p = p := by
    intro p
    unfold C6.actR
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ), Matrix.one_mul,
      Matrix.one_mul]
    rfl
  have hθ : ∀ θ, D.IsNormCut S γ (D.muR S γ 1) θ → ∀ p, S.inSS p → θ p = 1 := by
    intro θ hθ p hp
    have h := hθ.2.2 p hp
    rw [hR, integral_dirac] at h
    simpa [hact] using h
  unfold D.orbJ
  split_ifs with hex
  · have h1 := hθ _ hex.choose_spec.1
    calc ∫ p, hex.choose p • D.orbIntegrand S γ F p ∂S.μSS = ∫ p, D.orbIntegrand S γ F p ∂S.μSS := by
          refine integral_congr_ae ?_
          filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S] with p hp
          rw [h1 p hp, one_smul]
      _ = B.Jtau S (1, 1) F γ := rfl
      _ = B.JF S F γ := Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ
  · have hni : ¬ Integrable (fun p => D.orbIntegrand S γ F p) S.μSS := by
      intro hI
      apply hex
      refine ⟨fun _ => 1, ⟨measurable_const, fun _ => zero_le_one, fun p _ => ?_⟩, by simpa using hI⟩
      rw [hR, integral_dirac]
    rw [← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ]
    exact (integral_undef hni).symm

theorem vector_level_zero_eq_jacquet (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ)
    (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) (γ0 : B.Mat k ρ) (hγ0 : γ0 ∈ B.GV k ρ)
    (hZ : Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1)) (hD : D.IsDFrame B0 ν m γ0) :
    D.vecV B0 ν m Φ [(1, ζ)] = B.JF B0 Φ γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hloc := isLocPt_one hζ0
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k 0 Wp Wq B0 ν m Φ [(1, ζ)] hloc γ0 hb hG hγ0 hZ hD]
  have hw : (hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) = 1 := by
    refine Equiv.ext fun a => Fin.ext ?_
    have h1 := a.isLt
    have h2 := ((hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) a).isLt
    simp only [Equiv.Perm.coe_one, id]
    omega
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' [(1, ζ)] (0 + 1) hloc.2 hloc.1
  rw [hw] at hmono
  have hpos : 0 < Gf k 0 B0.z B0.z' γ0 := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k 0 _ _ [(1, ζ)] γ0 hloc hZ]; exact hG
  rw [hw]
  exact orbJ_one_eq B0 hγ0 hpos hnz (hZ.trans hmono) Φ

theorem vector_level_zero_degenerate (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ) (hζ : Complex.normSq ζ ≤ Tz k ρ B0.z * Tz k ρ B0.z') :
    D.vecV B0 ν m Φ [(1, ζ)] = 0 := by
  subst hρ
  unfold D.vecV
  rw [dif_neg]
  rintro ⟨_, h⟩
  rw [ptG_one] at h
  linarith

theorem exists_frame_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (ζ : ℂ) (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) :
    ∃ γ0 ∈ B.GV k ρ, Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1) ∧ D.IsDFrame B0 ν m γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  exact Formalism.FourierDecayAlt.P.exists_isotropic_frame k 0 Wp Wq B0 ν m [(1, ζ)] hb (isLocPt_one hζ0) hG

theorem jacquet_integral_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (hN : B0.μN = D.muN k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ) :
    B.JF B0 Φ γ = ∫ p : Mt k ρ × Mt k ρ, (B0.π (Matrix.of p.1)).comp
      ((Φ ((Matrix.of p.1)⁻¹ * γ * Matrix.of p.2)).comp (B0.π' (Matrix.of p.2)⁻¹)) ∂(B0.μW.prod B0.μW') := by
  subst hρ
  have : SigmaFinite B0.μW := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW
  have : SigmaFinite B0.μW' := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW'
  have hN0 : B0.μN = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := hN
  have hmeas : (B0.μW.prod B0.μN).prod (B0.μW'.prod B0.μN) = (B0.μW.prod B0.μW').map
      (fun p : Mt k 0 × Mt k 0 => ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) := by
    rw [hN0, Measure.prod_dirac, Measure.prod_dirac,
      Measure.map_prod_map (f := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0)))
        (g := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0))) _ _ (by fun_prop) (by fun_prop)]
    rfl
  have hemb : MeasurableEmbedding (fun p : Mt k 0 × Mt k 0 =>
      ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) :=
    (MeasurableEmbedding.id.prodMk_right _).prodMap (MeasurableEmbedding.id.prodMk_right _)
  have hpsi : ∀ (z : Fin (2 * 0 + k + 1) → ℂ) (g : B.Mat k 0), Formalism.QuantumDeterminants.psi k 0 z cStd g = 1 := by
    intro z g; simp [Formalism.QuantumDeterminants.psi, Formalism.QuantumDeterminants.ell]
  unfold B.JF besselJ
  rw [hmeas, hemb.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hpsi, star_one, mul_one, one_smul, Equiv.apply_symm_apply, inv_one]

end lev0

end Formalism.FourierDecayAlt.P.PBM
