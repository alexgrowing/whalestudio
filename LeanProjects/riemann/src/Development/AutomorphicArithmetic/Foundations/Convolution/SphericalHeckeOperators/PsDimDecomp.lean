import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem psDim_conj (σ : Equiv.Perm (Fin n)) {z : GL (Fin n) F} (hz : z ∈ iwahori F n)
    (hz' : z ∈ Parabolic.oppositeUnipotentRadical F n (id : Fin n → Fin n)) :
    (permGL F σ)⁻¹ * z * permGL F σ ∈ iwahori F n := by
  have hent : ∀ i j, (((permGL F σ)⁻¹ * z * permGL F σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (z : Matrix (Fin n) (Fin n) F) (σ i) (σ j) := by
    intro i j
    rw [← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply, inv_inv]
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hz
  have h4 := (Parabolic.mem_oppositeUnipotentRadical.1 hz').1
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [hent]; exact h1 _ _
  · rw [hent]
    rcases lt_trichotomy (σ i) (σ j) with h | h | h
    · rw [h4 _ _ h, map_zero]; exact zero_lt_one
    · exact absurd (σ.injective h) hij.ne'
    · exact h2 _ _ h
  · rw [hent]; exact h3 _

private theorem psDim_decomp (g : GL (Fin n) F) :
    ∃ p : blockUpper F n (id : Fin n → Fin n), ∃ σ : Equiv.Perm (Fin n), ∃ y ∈ iwahori F n,
      g = (p : GL (Fin n) F) * (permGL F σ * y) := by
  obtain ⟨p, k, hk, rfl⟩ := exists_borel_mul g
  have hk' : k ∈ (integralGL F n : Set (GL (Fin n) F)) := hk
  rw [integralGL_eq_iUnion_doubleCoset_permGL] at hk'
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 hk'
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hσ
  obtain ⟨u, hu, t, ht, z, hz, rfl⟩ := Parabolic.iwahoriFactorization_symm
    (Parabolic.iwahori_iwahoriFactorization (F := F) (β := (id : Fin n → Fin n)) monotone_id) x hx
  refine ⟨p * ⟨u, Parabolic.unipotentRadical_le_blockUpper hu.2⟩ * ⟨t, Parabolic.levi_le_blockUpper ht.2⟩, σ,
    (permGL F σ)⁻¹ * z * permGL F σ * y, mul_mem (psDim_conj σ hz.1 hz.2) hy, ?_⟩
  simp only [Subgroup.coe_mul]
  group

end

theorem UpperTheory.ConvolutionTheory.H.psDim :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (z : Fin n → ℂˣ),
      FiniteDimensional ℂ (psI F z) ∧ Module.finrank ℂ (psI F z) ≤ n.factorial := by
  intro F _ _ _ _ n z
  let L : psI F z →ₗ[ℂ] (Equiv.Perm (Fin n) → ℂ) :=
    { toFun := fun f σ => (f : GL (Fin n) F → ℂ) (permGL F σ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨p, σ, y, hy, rfl⟩ := psDim_decomp g
    have h0 : (f : GL (Fin n) F → ℂ) (permGL F σ) = 0 := congrFun hf σ
    rw [(mem_principalSeriesSpace.1 f.2.1).1 p, f.2.2 _ y hy, h0, mul_zero]
    rfl
  refine ⟨FiniteDimensional.of_injective L hL, ?_⟩
  have := LinearMap.finrank_le_finrank_of_injective hL
  simpa [Fintype.card_perm] using this
