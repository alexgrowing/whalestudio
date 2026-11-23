import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {O R R' D : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [Group D]

private theorem map_ofGL (f : R →+* R') (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  simp only [GG.map, GG.ofGL, SemidirectProduct.map_inl]

private theorem conj_push (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG 3 R) (g : D) :
    conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g =
      GG.map (φ : R →+* R') (conjBy h⁻¹ r g) := by
  simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MulAut.conj_inv_apply, map_mul, map_inv, map_ofGL]

private theorem conj_push_mat (φ : R →ₐ[O] R') (h : GL (Fin 3) R) (r : D →* GG 3 R) (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (φ : R →+* R') h)⁻¹ (push φ r) g).mat a b =
      φ ((conjBy h⁻¹ r g).mat a b) := by
  rw [conj_push]
  simp [GG.mat, GG.map, SemidirectProduct.map_left]

private theorem triIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG 3 R} {h : GL (Fin 3) R} (H : TriIn η Ψ I r h) :
    TriIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) where
  tri g hg a b hab := by rw [conj_push_mat, H.tri g hg a b hab, map_zero]
  ine s hs hη a := by rw [conj_push_mat, H.ine s hs hη a, AlgHom.commutes]

private theorem diagIn_push (φ : R →ₐ[O] R') {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D}
    {r : D →* GG 3 R} {h : GL (Fin 3) R} (H : DiagIn η Ψ I r h) :
    DiagIn η Ψ I (push φ r) (GeneralLinearGroup.map (φ : R →+* R') h) where
  toTriIn := triIn_push φ H.toTriIn
  low g hg a b hab := by rw [conj_push_mat, H.low g hg a b hab, map_zero]

variable [IsLocalRing O] [IsCO O R] [IsCO O R']

private theorem inHat_push (φ : R →ₐ[O] R') {h : GL (Fin 3) R} (H : InHat h) :
    InHat (GeneralLinearGroup.map (φ : R →+* R') h) := by
  have hm : ∀ x ∈ maximalIdeal R, φ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  unfold InHat CongOne EntIn at H ⊢
  intro a b
  have e : ((GeneralLinearGroup.map (φ : R →+* R') h : Matrix (Fin 3) (Fin 3) R') - 1) a b =
      φ (((h : Matrix (Fin 3) (Fin 3) R) - 1) a b) := by
    by_cases hab : a = b <;> simp [Matrix.sub_apply, Matrix.one_apply, hab]
  rw [e]
  exact hm _ (H a b)

end SlopeTestRemainingChoices

theorem UpperTheory.locAt_push_of_locAt :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (φ : R →ₐ[O] R') (v : ι) (r : F.D v →* GG 3 R), F.LocAt v r → F.LocAt v (push φ r) := by
  intro O _ _ G Γ ι _ _ F R R' _ _ _ _ _ _ φ v r hr
  unfold Frame.LocAt at hr ⊢
  obtain ⟨hT, hD, hU⟩ := hr
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨h, hh, ht⟩ := hT hv
    exact ⟨_, inHat_push φ hh, triIn_push φ ht⟩
  · obtain ⟨h, hh, ht⟩ := hD hv
    exact ⟨_, inHat_push φ hh, diagIn_push φ ht⟩
  · intro s hs
    have h1 := hU hv s hs
    simp only [push, MonoidHom.comp_apply, h1, map_one]
