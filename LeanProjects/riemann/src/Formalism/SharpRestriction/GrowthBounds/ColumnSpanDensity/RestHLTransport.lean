import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure RSIso {p n' : ℕ} (R₁ R₂ : RS p n') where
  φW : R₁.W ≃+* R₂.W
  φQ : R₁.Qq ≃+* R₂.Qq
  φO : R₁.O ≃+* R₂.O
  φK : R₁.Kf ≃+* R₂.Kf
  hWQ : ∀ x, φQ (algebraMap R₁.W R₁.Qq x) = algebraMap R₂.W R₂.Qq (φW x)
  hOK : ∀ x, φK (algebraMap R₁.O R₁.Kf x) = algebraMap R₂.O R₂.Kf (φO x)
  hι : ∀ x, φK (R₁.ι x) = R₂.ι (φQ x)
  hσ : ∀ x, φQ (R₁.σ x) = R₂.σ (φQ x)
  hj : ∀ x, φO (R₁.jO x) = R₂.jO (φW x)
  hw : φO R₁.w = R₂.w

def RestRSIso : Prop := ∀ (p n' : ℕ) (R₁ R₂ : RS p n'), Nonempty (RSIso R₁ R₂)

def RestHLTransport : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (I : RSIso R₁ R₂) (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ),
    ∃ (Φ : Submodule R₁.W (Fin (m + 1) → R₁.Qq) ≃ Submodule R₂.W (Fin (m + 1) → R₂.Qq))
      (Ψ : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0),
      (∀ (c : R₁.Kf) v, Ψ (c • v) = I.φK c • Ψ v) ∧
      (∀ L, IsLattice R₁.W L ↔ IsLattice R₂.W (Φ L)) ∧
      (∀ (r : ℕ) (e : Edge R₁.W R₁.Qq (m + 1)), IsEdge p n' r e ↔ IsEdge p n' r ⟨Φ e.src, Φ e.tgt⟩) ∧
      (∀ L x, x ∈ HL (O := R₁.O) R₁.ι R₁.σ lam0 L ↔ Ψ x ∈ HL (O := R₂.O) R₂.ι R₂.σ lam0 (Φ L)) ∧
      (∀ (e : Edge R₁.W R₁.Qq (m + 1)) x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 e ↔
        Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 ⟨Φ e.src, Φ e.tgt⟩) ∧
      dimV R₁.Kf lam0 = dimV R₂.Kf lam0

section Formal

variable {O₁ K₁ V₁ O₂ K₂ V₂ : Type*} [CommRing O₁] [Field K₁] [Algebra O₁ K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Module O₁ V₁] [IsScalarTower O₁ K₁ V₁] [CommRing O₂] [Field K₂] [Algebra O₂ K₂] [AddCommGroup V₂] [Module K₂ V₂]
  [Module O₂ V₂] [IsScalarTower O₂ K₂ V₂] (φO : O₁ ≃+* O₂) (φK : K₁ ≃+* K₂) (Ψ : V₁ ≃+ V₂)

theorem sl_symm (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₂) (v : V₂) :
    Ψ.symm (c • v) = φK.symm c • Ψ.symm v := by
  apply Ψ.injective
  rw [hΨ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

def dT (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (G : Module.Dual K₁ V₁) : Module.Dual K₂ V₂ where
  toFun v := φK (G (Ψ.symm v))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' c x := by
    rw [sl_symm φK Ψ hΨ, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, RingHom.id_apply, smul_eq_mul]

theorem dT_apply (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (G : Module.Dual K₁ V₁) (v : V₁) : dT φK Ψ hΨ G (Ψ v) = φK (G v) := by
  show φK (G (Ψ.symm (Ψ v))) = _
  rw [AddEquiv.symm_apply_apply]

theorem dT_smul (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₁) (G : Module.Dual K₁ V₁) : dT φK Ψ hΨ (c • G) = φK c • dT φK Ψ hΨ G := by
  ext v
  show φK ((c • G) (Ψ.symm v)) = φK c • φK (G (Ψ.symm v))
  rw [LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem sl_scale (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c : K₁) {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {x : V₁}
    (hx : x ∈ scale c M) : Ψ x ∈ scale (φK c) M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨Ψ y, (h y).1 hy, (hΨ c y).symm⟩

theorem sl_scale2 (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (c d : K₁) {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {x : V₁}
    (hx : x ∈ scale c (scale d M)) : Ψ x ∈ scale (φK c) (scale (φK d) M') := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨Ψ y, sl_scale φK Ψ hΨ d h hy, (hΨ c y).symm⟩

theorem sl_dual (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (hOK : ∀ x, φK (algebraMap O₁ K₁ x) = algebraMap O₂ K₂ (φO x)) {M : Submodule O₁ V₁}
    {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {G : Module.Dual K₁ V₁}
    (hG : G ∈ Formalism.GradedWeylDivisibility.dualLat O₁ K₁ M) : dT φK Ψ hΨ G ∈ Formalism.GradedWeylDivisibility.dualLat O₂ K₂ M' := by
  intro v hv
  have h1 : Ψ.symm v ∈ M := (h _).2 (by rwa [AddEquiv.apply_symm_apply])
  obtain ⟨a, ha⟩ := hG _ h1
  exact ⟨φO a, by show _ = φK (G (Ψ.symm v)); rw [← ha, hOK]⟩

theorem sl_scale_dual (hΨ : ∀ (c : K₁) v, Ψ (c • v) = φK c • Ψ v) (hOK : ∀ x, φK (algebraMap O₁ K₁ x) = algebraMap O₂ K₂ (φO x)) (c : K₁)
    {M : Submodule O₁ V₁} {M' : Submodule O₂ V₂} (h : ∀ x, x ∈ M ↔ Ψ x ∈ M') {G : Module.Dual K₁ V₁}
    (hG : G ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O₁ K₁ M)) :
    dT φK Ψ hΨ G ∈ scale (φK c) (Formalism.GradedWeylDivisibility.dualLat O₂ K₂ M') := by
  obtain ⟨G₀, hG₀, rfl⟩ := hG
  exact ⟨dT φK Ψ hΨ G₀, sl_dual φO φK Ψ hΨ hOK h hG₀, (dT_smul φK Ψ hΨ c G₀).symm⟩

end Formal

end Formalism.MainNotions.flipOneThree.Pf

end
