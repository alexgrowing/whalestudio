import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LengthInverseBound
import Formalism.LocalToGlobal.HermitianForms.PrkSmul

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open NumberField Formalism.UG Matrix

variable {E : Type} [Field E] [NumberField E]

theorem sig_natInv (σ : E →+* E) (T : ℕ) : σ ((T : E)⁻¹) = (T : E)⁻¹ := by
  simp [map_inv₀, map_natCast]

theorem galois_image_integers (σ : E →+* E) (r : 𝓞 E) : σ (r : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨σ (r : E), (r.2).map σ.toIntAlgHom⟩, rfl⟩

theorem fix_orthogonal_vector {N N' : ℕ} (σ : E →+* E) (hσ : ∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x))
    (J : Matrix (Fin N) (Fin N) E) (J' : Matrix (Fin N') (Fin N') E)
    (hdef : ∀ (φ : E →+* ℂ) (x : Fin N → E), ∃ r : ℝ, 0 ≤ r ∧ φ (hform σ J x x) = r ∧ (r = 0 → x = 0))
    (ι : (Fin N' → E) →ₗ[E] (Fin N → E)) (z0 : Fin N → E)
    (hiso : ∀ x x', hform σ J (ι x) (ι x') = hform σ J' x x')
    (horth : ∀ x, hform σ J (ι x) z0 = 0 ∧ hform σ J z0 (ι x) = 0)
    (hspan : ∀ y, ∃ (x : Fin N' → E) (s : E), y = ι x + s • z0)
    (T : ℕ) (hTp : T.Prime) (hdeg : Module.finrank ℚ E < T - 1) (hzz : hform σ J z0 z0 = T)
    (L1 L2 : Submodule (𝓞 E) (Fin N' → E))
    (hsd2 : (∀ y, (∀ x ∈ L2, hform σ J' x y ∈ (algebraMap (𝓞 E) E).range) → y ∈ L2) ∧
      ∀ x ∈ L2, ∀ y ∈ L2, hform σ J' x y ∈ (algebraMap (𝓞 E) E).range)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y)
    (hlat : Formalism.L2.Forms.mulLat γ (L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) =
      L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0})
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hTP : (T : 𝓞 E) ∈ P)
    (hres : ∀ y : Fin N → E, (∀ w ∈ L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
        hform σ J w y ∈ (algebraMap (𝓞 E) E).range) →
      ∀ r r' : 𝓞 E, (r : E) = hform σ J z0 y → (r' : E) = hform σ J z0 (γ *ᵥ y) → r - r' ∈ P) :
    γ *ᵥ z0 = z0 := by
  have hT1 : 1 < T := hTp.one_lt
  have hT0 : (T : E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  set z' : Fin N → E := (T : E)⁻¹ • z0 with hz'
  have hz0 : z0 = (T : E) • z' := by rw [hz', smul_smul, mul_inv_cancel₀ hT0, one_smul]

  have hzz' : (T : E) * hform σ J z' z' = 1 := by
    rw [hz', hform_smul_left, hform_smul_right, hzz, sig_natInv]; field_simp
  have hz0z' : hform σ J z0 z' = 1 := by
    rw [hz', hform_smul_right, hzz]; field_simp

  have memL : ∀ (L : Submodule (𝓞 E) (Fin N' → E)) w, w ∈ L.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} →
      ∃ l ∈ L, ∃ r : 𝓞 E, w = ι l + (r : E) • z0 := by
    intro L w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨l, hl, r, by rw [← algebraMap_smul E r z0]; rfl⟩

  have hd1 : ∀ w ∈ L1.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
      hform σ J w z' ∈ (algebraMap (𝓞 E) E).range := by
    intro w hw
    obtain ⟨l, _, r, rfl⟩ := memL L1 w hw
    rw [hform_add_left, hform_smul_left, hz', hform_smul_right, hform_smul_right, (horth l).1, hzz]
    have : (T : E)⁻¹ * 0 + σ (r : E) * ((T : E)⁻¹ * (T : E)) = σ (r : E) := by
      rw [mul_zero, zero_add, inv_mul_cancel₀ hT0, mul_one]
    rw [this]; exact galois_image_integers σ r

  have hd2 : ∀ w ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0},
      hform σ J w (γ *ᵥ z') ∈ (algebraMap (𝓞 E) E).range := by
    intro w hw
    rw [← hlat] at hw
    obtain ⟨w1, hw1, rfl⟩ := Submodule.mem_map.1 hw
    show hform σ J (γ *ᵥ w1) (γ *ᵥ z') ∈ _
    rw [hγ]; exact hd1 w1 hw1

  obtain ⟨y1, s, hys⟩ := hspan (γ *ᵥ z')
  have hy1 : y1 ∈ L2 := by
    apply hsd2.1
    intro x hx
    have hmem : ι x ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} :=
      Submodule.mem_sup_left (Submodule.mem_map.2 ⟨x, hx, rfl⟩)
    have := hd2 _ hmem
    rwa [hys, hform_add_right, hform_smul_right, (horth x).1, mul_zero, add_zero, hiso] at this
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, (t : E) = s * T := by
    have hmem : z0 ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self z0)
    have := hd2 _ hmem
    rw [hys, hform_add_right, hform_smul_right, (horth y1).2, hzz, zero_add] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht⟩
  have hyt : γ *ᵥ z' = ι y1 + (t : E) • z' := by
    rw [hys, ht, hz0, smul_smul]

  have hγzz : (T : E) * hform σ J (γ *ᵥ z') (γ *ᵥ z') = 1 := by rw [hγ]; exact hzz'
  have hmemy : γ *ᵥ z' ∈ L2.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z'} := by
    rw [hyt]
    refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨y1, hy1, rfl⟩) ?_
    have h := Submodule.smul_mem (Submodule.span (𝓞 E) {z'}) t (Submodule.mem_span_singleton_self z')
    rw [← algebraMap_smul E t z'] at h
    exact h
  have hint : ∀ x ∈ L2.map (ι.restrictScalars (𝓞 E)), ∃ a : 𝓞 E, (a : E) = hform σ J x x := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨a, ha⟩ := hsd2.2 l hl l hl
    refine ⟨a, ?_⟩
    show (a : E) = hform σ J (ι l) (ι l)
    rw [hiso]; exact ha
  have hzL : ∀ x ∈ L2.map (ι.restrictScalars (𝓞 E)), hform σ J x z' = 0 ∧ hform σ J z' x = 0 := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Submodule.mem_map.1 hx
    refine ⟨?_, ?_⟩
    · show hform σ J (ι l) z' = 0
      rw [hz', hform_smul_right, (horth l).1, mul_zero]
    · show hform σ J z' (ι l) = 0
      rw [hz', hform_smul_left, (horth l).2, mul_zero]
  obtain ⟨b, ⟨k, hk, hbk⟩, hb⟩ :=
    length_inverse_bound σ hσ J hdef (L2.map (ι.restrictScalars (𝓞 E))) hint z' hzL T hT1 hzz' (γ *ᵥ z') hmemy hγzz

  have hbP : b - 1 ∈ P := by
    have h1 := hres z' hd1 1 b (by rw [hz0z']; simp) (by rw [hb, hform_smul_right, hz0z', mul_one])
    have : b - 1 = -(1 - b) := by ring
    rw [this]; exact P.neg_mem h1
  have hb1 : b = 1 := root_eq_one P T k b hTp hP hTP hk hbk hbP hdeg
  rw [hb1] at hb
  have : γ *ᵥ z' = z' := by rw [hb]; simp
  rw [hz0, Matrix.mulVec_smul, this]

theorem fix_restrict {N N' : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (J' : Matrix (Fin N') (Fin N') E)
    (ι : (Fin N' → E) →ₗ[E] (Fin N → E)) (hinj : Function.Injective ι) (z0 : Fin N → E)
    (hiso : ∀ x x', hform σ J (ι x) (ι x') = hform σ J' x x')
    (horth : ∀ x, hform σ J (ι x) z0 = 0 ∧ hform σ J z0 (ι x) = 0)
    (hspan : ∀ y, ∃ (x : Fin N' → E) (s : E), y = ι x + s • z0)
    (hzz : hform σ J z0 z0 ≠ 0)
    (γ : Matrix (Fin N) (Fin N) E) (hγ : ∀ x y, hform σ J (γ *ᵥ x) (γ *ᵥ y) = hform σ J x y) (hfix : γ *ᵥ z0 = z0) :
    ∃ δ : Matrix (Fin N') (Fin N') E, (∀ x, γ *ᵥ ι x = ι (δ *ᵥ x)) ∧
      ∀ x y, hform σ J' (δ *ᵥ x) (δ *ᵥ y) = hform σ J' x y := by
  have hrange : ∀ x, γ *ᵥ ι x ∈ LinearMap.range ι := by
    intro x
    obtain ⟨x', s, hs⟩ := hspan (γ *ᵥ ι x)
    have h0 : hform σ J (γ *ᵥ ι x) z0 = 0 := by
      conv_lhs => rw [← hfix]
      rw [hγ]; exact (horth x).1
    rw [hs, hform_add_left, hform_smul_left, (horth x').1, zero_add] at h0
    have hs0 : σ s = 0 := (mul_eq_zero.1 h0).resolve_right hzz
    have : s = 0 := (map_eq_zero σ).1 hs0
    rw [hs, this, zero_smul, add_zero]; exact ⟨x', rfl⟩
  let e := LinearEquiv.ofInjective ι hinj
  let g : (Fin N' → E) →ₗ[E] LinearMap.range ι :=
    LinearMap.codRestrict (LinearMap.range ι) ((Matrix.mulVecLin γ).comp ι) hrange
  let f : (Fin N' → E) →ₗ[E] (Fin N' → E) := e.symm.toLinearMap.comp g
  have hf : ∀ x, ι (f x) = γ *ᵥ ι x := by
    intro x
    have h1 : (e (f x) : Fin N → E) = ι (f x) := rfl
    rw [← h1]
    show ((e (e.symm (g x)) : LinearMap.range ι) : Fin N → E) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨LinearMap.toMatrix' f, fun x => ?_, fun x y => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, hf]
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, ← hiso, hf, hf, hγ, hiso]

end Formalism.L2.GlobalTheoryTheory.Br
