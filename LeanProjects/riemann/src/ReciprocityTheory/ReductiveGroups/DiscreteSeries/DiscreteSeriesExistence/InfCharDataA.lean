import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

namespace ICD

instance closGen_completeSpace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) :
    CompleteSpace (closGen E V) := by
  unfold closGen; infer_instance

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem le_gen (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) : V ≤ genSub E V :=
  le_sInf fun _ hT => hT.1

theorem gen_stable {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {x : M} (hx : x ∈ genSub E V)
    (a b : Fin n) : E a b x ∈ genSub E V :=
  Submodule.mem_sInf.2 fun T hT => hT.2 a b x (Submodule.mem_sInf.1 hx T hT)

theorem gen_le {E : Fin n → Fin n → Module.End ℂ M} {V P : Submodule ℂ M} (h1 : V ≤ P)
    (h2 : ∀ a b, ∀ v ∈ P, E a b v ∈ P) : genSub E V ≤ P :=
  sInf_le ⟨h1, h2⟩

end Gen

theorem mem_closGen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} {x : D} (hx : x ∈ genSub E V) :
    (x : H) ∈ closGen E V :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hx)

section Ext

variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {C₁ : Submodule ℂ H₁} [C₁.HasOrthogonalProjection] {C₂ : Submodule ℂ H₂}

def ext (U : C₁ ≃ₗᵢ[ℂ] C₂) : H₁ →L[ℂ] H₂ :=
  C₂.subtypeL ∘L U.toLinearIsometry.toContinuousLinearMap ∘L C₁.orthogonalProjectionOnto

theorem ext_apply (U : C₁ ≃ₗᵢ[ℂ] C₂) (v : H₁) (hv : v ∈ C₁) : ext U v = ((U ⟨v, hv⟩ : C₂) : H₂) := by
  show ((U (C₁.orthogonalProjectionOnto v) : C₂) : H₂) = _
  exact congrArg (fun z : C₁ => ((U z : C₂) : H₂))
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := C₁) ⟨v, hv⟩)

theorem ext_apply' (U : C₁ ≃ₗᵢ[ℂ] C₂) (z : C₁) : ext U (z : H₁) = ((U z : C₂) : H₂) :=
  ext_apply U z z.2

theorem ext_mem (U : C₁ ≃ₗᵢ[ℂ] C₂) (v : H₁) : ext U v ∈ C₂ :=
  (U (C₁.orthogonalProjectionOnto v)).2

theorem ext_inj (U : C₁ ≃ₗᵢ[ℂ] C₂) {v w : H₁} (hv : v ∈ C₁) (hw : w ∈ C₁) (h : ext U v = ext U w) : v = w := by
  rw [ext_apply U v hv, ext_apply U w hw] at h
  have := U.injective (Subtype.ext h)
  exact congrArg Subtype.val this

theorem ext_intertw {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    {G : Set (Matrix (Fin n) (Fin n) ℂ)} (U : C₁ ≃ₗᵢ[ℂ] C₂)
    (hU : ∀ g ∈ G, ∀ x y : C₁, (x : H₁) = σ₁ g (y : H₁) → ((U x : C₂) : H₂) = σ₂ g ((U y : C₂) : H₂))
    (hst : ∀ g ∈ G, ∀ x ∈ C₁, σ₁ g x ∈ C₁) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) {x : H₁} (hx : x ∈ C₁) :
    ext U (σ₁ g x) = σ₂ g (ext U x) := by
  rw [ext_apply U _ (hst g hg x hx), ext_apply U x hx]
  exact hU g hg _ _ rfl

end Ext

section Deriv

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁} {E₁ : Fin n → Fin n → Module.End ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂} {E₂ : Fin n → Fin n → Module.End ℂ D₂}

theorem map_actM (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (Φ : H₁ →L[ℂ] H₂)
    (C₁ : Submodule ℂ H₁) (hint : ∀ g ∈ UJset ε, ∀ x ∈ C₁, Φ (σ₁ g x) = σ₂ g (Φ x))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (x : D₁) (hx : (x : H₁) ∈ C₁) (y : D₂)
    (hxy : Φ (x : H₁) = (y : H₂)) :
    Φ ((actM E₁ X x : D₁) : H₁) = ((actM E₂ X y : D₂) : H₂) := by
  have h1 := (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD₁.deriv X hX x)
  have h2 := hD₂.deriv X hX y
  refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  show Φ (σ₁ (NormedSpace.exp ((t : ℂ) • X)) (x : H₁)) = σ₂ (NormedSpace.exp ((t : ℂ) • X)) (y : H₂)
  rw [hint _ (exp_smul_mem_UJset hX t) _ hx, hxy]

theorem E_eq_actM {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    E a b = actM E ((1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε)) +
      Complex.I • actM E ((-Complex.I / 2 : ℂ) •
        (Matrix.single a b (1 : ℂ) + Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε)) := by
  rw [← matrixAction_smul, ← matrixAction_add, ← matrix_decomp_lieAlgebra ε (Matrix.single a b (1 : ℂ)), matrixAction_single]

theorem map_E (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (Φ : H₁ →L[ℂ] H₂)
    (C₁ : Submodule ℂ H₁) (hint : ∀ g ∈ UJset ε, ∀ x ∈ C₁, Φ (σ₁ g x) = σ₂ g (Φ x))
    (x : D₁) (hx : (x : H₁) ∈ C₁) (y : D₂) (hxy : Φ (x : H₁) = (y : H₂)) (a b : Fin n) :
    Φ ((E₁ a b x : D₁) : H₁) = ((E₂ a b y : D₂) : H₂) := by
  rw [E_eq_actM ε E₁ a b, E_eq_actM ε E₂ a b]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul]
  rw [map_actM hD₁ hD₂ Φ C₁ hint (hermPart_mem_lieAlgebra ε _) x hx y hxy,
    map_actM hD₁ hD₂ Φ C₁ hint (hermPart_mem_lieAlgebra_var ε _) x hx y hxy]

end Deriv

section KType

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem ktype_map (C₁ : Submodule ℂ H₁) (Φ : H₁ →ₗ[ℂ] H₂)
    (hinj : ∀ x ∈ C₁, ∀ y ∈ C₁, Φ x = Φ y → x = y)
    (hint : ∀ g ∈ Kset ε, ∀ x ∈ C₁, Φ (σ₁ g x) = σ₂ g (Φ x))
    (hst : ∀ g ∈ Kset ε, ∀ x ∈ C₁, σ₁ g x ∈ C₁)
    {Λ : Fin n → ℝ} {S : Submodule ℂ H₁} (hS : S ≤ C₁) (h : Formalism.MainNotions.S.IsKTypeOf ε σ₁ Λ S) :
    Formalism.MainNotions.S.IsKTypeOf ε σ₂ Λ (S.map Φ) := by
  obtain ⟨hfd, hK, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := h
  have := hfd
  have hK' : ∀ g, g ∈ Formalism.REAL.Kset ε → g ∈ Kset ε := fun g hg => by rwa [mir_Kset_eq] at hg
  have hne : ∀ x ∈ S, x ≠ 0 → Φ x ≠ 0 := by
    intro x hx hx0 h0
    exact hx0 (hinj x (hS hx) 0 (zero_mem _) (by rw [h0, map_zero]))
  refine ⟨inferInstance, ?_, ?_, ⟨Φ v, Submodule.mem_map_of_mem hvS, hne v hvS hv0, ?_⟩, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ₁ g x, hK g hg x hx, hint g (hK' g hg) x (hS hx)⟩
  · intro S' hS' hS'K
    have hT : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x ∈ S ⊓ S'.comap Φ, σ₁ g x ∈ S ⊓ S'.comap Φ := by
      rintro g hg x ⟨hx, hx'⟩
      refine ⟨hK g hg x hx, ?_⟩
      show Φ (σ₁ g x) ∈ S'
      rw [hint g (hK' g hg) x (hS hx)]
      exact hS'K g hg _ hx'
    rcases hirr (S ⊓ S'.comap Φ) inf_le_left hT with h0 | h1
    · left
      refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := hS' hy
      have : x ∈ S ⊓ S'.comap Φ := ⟨hx, hy⟩
      rw [h0, Submodule.mem_bot] at this
      rw [this, map_zero]
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ S ⊓ S'.comap Φ := by rw [h1]; exact hx
      exact this.2
  · intro θ hθ
    rw [← hint _ (hK' _ hθ) v (hS hvS), hvw θ hθ, map_smul]
  · rintro μ _ ⟨x, hx, rfl⟩ hx0 hw
    refine hdom μ x hx (fun h0 => hx0 (by rw [h0, map_zero])) fun θ hθ => ?_
    refine hinj _ (hst _ (hK' _ hθ) x (hS hx)) _ (C₁.smul_mem _ (hS hx)) ?_
    rw [hint _ (hK' _ hθ) x (hS hx), hw θ hθ, map_smul]

end KType

end ICD

end ReciprocityTheory.ChartRestriction.DS
