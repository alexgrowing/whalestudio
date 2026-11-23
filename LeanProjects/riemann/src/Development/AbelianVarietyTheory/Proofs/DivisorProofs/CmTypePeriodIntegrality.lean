import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.ScaledRestr

theorem inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) := inferInstance
  unfold inK
  rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors O)]
  intro c
  intro x y hxy
  exact smul_right_injective H (nonZeroDivisors.coe_ne_zero c) hxy

theorem exists_scaled_image {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {H : Type} [AddCommGroup H] [Module O H] {I : Type}
    (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (D : O) (e f : I → H)
    (hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ) (hG : IsGens φ ρ e f)
    (N : Module.End K (K ⊗[O] H)) (i : I) (hN : IsLower ρ (φ i) (e i) (f i) N) (h : H) :
    ∃ m : H, inK K H m = algebraMap O K D • N (inK K H h) := by
  have key : ∀ x ∈ ⨆ σ : E →+* K, eigLat ρ σ, ∃ m : H, inK K H m = N (inK K H x) := by
    intro x hx
    refine Submodule.iSup_induction (fun σ : E →+* K => eigLat ρ σ)
      (motive := fun x => ∃ m : H, inK K H m = N (inK K H x)) hx ?_ ?_ ?_
    · intro σ x hx
      by_cases hσ : σ = φ i
      · subst hσ
        rw [(hG i).1, Submodule.mem_span_singleton] at hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨u • f i, ?_⟩
        rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul_of_tower, hN.1]
      · refine ⟨0, ?_⟩
        have hx' : inK K H x ∈ eigK ρ σ := hx
        rw [hN.2 σ hσ _ hx', LinearMap.map_zero]
    · exact ⟨0, by simp⟩
    · intro x y hx hy
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, ha, hb]⟩
  obtain ⟨m, hm⟩ := key _ (hD h)
  refine ⟨m, ?_⟩
  rw [hm, LinearMap.map_smul, LinearMap.map_smul_of_tower, algebraMap_smul]

end GlobalTheory.ScaledRestr

namespace GlobalTheory.ScaledRestr

theorem scaledRestr_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → ∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hlat hEig e f hG N hN i
  haveI : Module.Free O H := hlat.1
  have hinj := inK_injective (O := O) K H
  have hD : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ := hEig.2.2.1.2
  let g : H →ₗ[O] K ⊗[O] H := (algebraMap O K D) • ((N i).restrictScalars O ∘ₗ inK K H)
  have hg : ∀ h, g h ∈ LinearMap.range (inK K H) := by
    intro h
    obtain ⟨m, hm⟩ := exists_scaled_image φ ρ D e f hD hG (N i) i (hN i) h
    exact ⟨m, hm⟩
  refine ⟨(LinearEquiv.ofInjective (inK K H) hinj).symm.toLinearMap ∘ₗ (g.codRestrict _ hg), ?_, ?_⟩
  · intro h
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this
  · intro M hM
    ext h
    apply hinj
    rw [hM h]
    have := (LinearEquiv.ofInjective (inK K H) hinj).apply_symm_apply (g.codRestrict _ hg h)
    rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at this
    simpa [g] using this.symm

end GlobalTheory.ScaledRestr
