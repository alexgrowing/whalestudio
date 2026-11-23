import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

private theorem norm_lt_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : x ∈ maximalIdeal c.O) :
    ‖(x : Qbar l)‖ < 1 := by
  haveI := c.dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hcast : (((l : ℕ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := map_natCast c.O.val l
  have hlne : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h1 : (((l : ℕ) : c.O) : Qbar l) = 0 := by rw [h0]; rfl
    rw [hcast] at h1
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)
  obtain ⟨e, u, hle⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlne hϖ
  obtain ⟨a, v, hxa⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hlt := GlobalTheory.CoefCoord.norm_natCast_lt_one (l := l)
  have he : e ≠ 0 := by
    rintro rfl
    have hu := GlobalTheory.CoefCoord.norm_unit c u
    rw [pow_zero, mul_one] at hle
    rw [← hle, hcast] at hu
    linarith
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hxa
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hxa] at hx
    exact hx v.isUnit
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha
  have key : x ^ e = ((l : ℕ) : c.O) * (↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e)) := by
    rw [hxa, hle]
    linear_combination (-(↑v ^ e * ϖ ^ e * ϖ ^ (a' * e))) * u.mul_inv
  have h2 : ‖(x : Qbar l)‖ ^ e
      = ‖(((l : ℕ) : c.O) : Qbar l)‖ * ‖((↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e) : c.O) : Qbar l)‖ := by
    rw [← norm_pow, ← norm_mul, ← SubmonoidClass.coe_pow, ← MulMemClass.coe_mul, key]
  have h3 := GlobalTheory.CoefCoord.norm_le_one c (↑u⁻¹ * ↑v ^ e * ϖ ^ (a' * e))
  have h4 : ‖(x : Qbar l)‖ ^ e < 1 := by
    rw [h2, hcast]
    calc _ ≤ ‖((l : ℕ) : Qbar l)‖ * 1 := by gcongr
      _ < 1 := by simpa using hlt
  by_contra hge
  push_neg at hge
  exact absurd h4 (not_lt.mpr (one_le_pow₀ hge))

private theorem map_mem_max {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (ξ : R →ₐ[O] O) (x : R) (hx : x ∈ maximalIdeal R) : ξ x ∈ maximalIdeal O := by
  by_contra h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  obtain ⟨u, hu⟩ := h
  have hy : ξ (x * algebraMap O R (↑u⁻¹ : O) - 1) = 0 := by
    rw [map_sub, map_mul, AlgHom.commutes, ← hu, map_one]
    simp
  have hm : x * algebraMap O R (↑u⁻¹ : O) - 1 ∈ maximalIdeal R := by
    by_contra h2
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h2
    have h3 := h2.map ξ
    rw [hy] at h3
    exact not_isUnit_zero h3
  have h1 : (1 : R) ∈ maximalIdeal R := by
    have h4 := (maximalIdeal R).sub_mem ((maximalIdeal R).mul_mem_right (algebraMap O R ↑u⁻¹) hx) hm
    simpa using h4
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem not_irr_of_line {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 3) k) (j : Fin 3)
    (h : ∀ s i, i ≠ j → (r s).val i j = 0) : ¬ IsIrr r := by
  intro hI
  obtain ⟨-, -, hmin⟩ := hI
  have hinv : Formalism.MainNotions.N.IsInv r (Submodule.span k {Pi.single j (1 : k)}) := by
    intro g v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine Submodule.mem_span_singleton.mpr ⟨a * (r g).val j j, ?_⟩
    ext i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, hij, h g i hij]
  rcases hmin _ le_top hinv with h0 | htop
  · have hs : (Pi.single j (1 : k) : Fin 3 → k) = 0 := by
      rw [← Submodule.mem_bot k, ← h0]
      exact Submodule.mem_span_singleton_self _
    have := congrFun hs j
    simp at this
  · have hj : j + 1 ≠ j := by fin_cases j <;> decide
    have hmem : (Pi.single (j + 1) (1 : k) : Fin 3 → k) ∈ Submodule.span k {Pi.single j (1 : k)} := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun ha (j + 1)
    simp [Pi.single_apply, hj] at this

private theorem ti_of {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Fr.Frame l k} {K : Type} [CommRing K]
    (ρ : Fr.NRep F 3 K) (p : Ideal K) (H : ∀ j : Fin 3, ¬ ∀ g i, i ≠ j → ρ.r g i j ∈ p) : ρ.TI p := by
  refine ⟨⟨fun hle => H 0 ?_, fun hle => H 2 ?_⟩, fun _ hle => H 1 ?_⟩
  · intro g i hi
    exact hle (Ideal.subset_span ⟨g, i, 0, by revert hi; fin_cases i <;> decide, rfl⟩)
  · intro g i hi
    exact hle (Ideal.subset_span ⟨g, i, 2, by revert hi; fin_cases i <;> decide, rfl⟩)
  · intro g i hi
    refine hle (Ideal.subset_span ⟨g, i, 1, ?_, rfl⟩)
    revert hi
    fin_cases i <;> simp [Fr.w] <;> decide

end UpperTheory.V.J

theorem UpperTheory.V.J.xiTI :
    UpperTheory.V.J.XiTI := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R ξ r hr hi
  have hcol : ∀ j : Fin 3, ¬ ∀ g i, i ≠ j → ξ (R.S.ρ.r g i j) = 0 := by
    intro j h
    refine not_irr_of_line r j (fun s i hij => ?_) hi
    rw [hr s]
    exact congrArg Subtype.val (h (k.p0 s) i hij)
  refine ⟨ti_of _ _ fun j h => hcol j fun g i hij => h g i hij, ⟨fun a => GlobalTheory.CoefCoord.norm_le_one c₁ _,
    fun b hb => norm_lt_of_mem c₁ _ (map_mem_max ξ b.1 hb)⟩, ti_of _ _ fun j h => hcol j fun g i hij => ?_⟩
  have h0 : ptA R ξ (R.S.u.r g i j) = 0 := h g i hij
  exact Subtype.ext h0

end
