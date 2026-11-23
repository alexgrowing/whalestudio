import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.PrimConst

open NumberField

theorem exists_dividing {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    {ι : Type} (c : ι → Ω) (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] (D : ℕ) (hD : 0 < D)
    (hc : ∀ i, c i ∈ E ∧ IsIntegral ℤ ((D : Ω) * c i))
    (hne : ∃ i, c i ≠ 0) : ∃ i0, c i0 ≠ 0 ∧ ∀ i, c i * (c i0)⁻¹ ∈ A := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NumberField E := by
    refine { to_charZero := inferInstance, to_finiteDimensional := ?_ }
    convert ‹FiniteDimensional ℚ E›
    exact Subsingleton.elim _ _
  have hmem : ∀ i, (D : Ω) * c i ∈ E := fun i => E.mul_mem (E.natCast_mem D) (hc i).1
  let f : ι → 𝓞 E := fun i => ⟨⟨(D : Ω) * c i, hmem i⟩, by
      rw [mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) E.val.injective).1 (hc i).2⟩
  have hf : ∀ i, algebraMap (𝓞 E) Ω (f i) = (D : Ω) * c i := fun i => rfl
  obtain ⟨s0, hs0⟩ : ∃ s0 : Finset ι, ∀ i, f i ∈ Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) := by
    have hN : IsNoetherian ℤ (𝓞 E) := inferInstance
    obtain ⟨M, ⟨s0, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 hN
      (Set.range fun s : Finset ι => Submodule.span ℤ ((s.image f : Finset (𝓞 E)) : Set (𝓞 E))) (Set.range_nonempty _)
    refine ⟨s0, fun i => ?_⟩
    have hle : Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) ≤
        Submodule.span ℤ (((insert i s0).image f : Finset (𝓞 E)) : Set (𝓞 E)) :=
      Submodule.span_mono (by intro y hy; simp only [Finset.coe_image, Finset.coe_insert] at hy ⊢; exact Set.image_mono (Set.subset_insert _ _) hy)
    have heq := eq_of_le_of_not_lt hle (hmax _ ⟨insert i s0, rfl⟩)
    rw [heq]; exact Submodule.subset_span (by simp)
  set v := A.valuation
  have hDv : v (D : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.2 hD.ne'
  have hint : ∀ z : ℤ, v (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  obtain ⟨i1, hi1⟩ := hne
  have ht : (s0.filter (fun i => c i ≠ 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hz : ∀ y ∈ s0.image f, y = 0 := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have := hcon hj; push_neg at this
      ext; simp [f, this]
    have h1 := hs0 i1
    rw [Submodule.mem_span_finset] at h1
    obtain ⟨g, -, hg⟩ := h1
    rw [Finset.sum_eq_zero (fun y hy => by rw [hz y hy, smul_zero])] at hg
    have := congrArg (algebraMap (𝓞 E) Ω) hg
    rw [hf, map_zero] at this
    exact hi1 ((mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hD.ne'))
  obtain ⟨i0, hi0t, hmax⟩ := (s0.filter (fun i => c i ≠ 0)).exists_max_image (fun i => v (c i)) ht
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0t).2
  have hmax' : ∀ j ∈ s0, v (c j) ≤ v (c i0) := by
    intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, map_zero]; exact zero_le'
    · exact hmax j (Finset.mem_filter.2 ⟨hj, hcj⟩)
  refine ⟨i0, hi0, fun i => ?_⟩
  have h1 := hs0 i
  rw [Submodule.mem_span_finset] at h1
  obtain ⟨g, -, hg⟩ := h1
  have h2 := congrArg (algebraMap (𝓞 E) Ω) hg
  rw [hf, map_sum] at h2
  have hle : v ((D : Ω) * c i) ≤ v (D : Ω) * v (c i0) := by
    rw [← h2]
    refine Valuation.map_sum_le _ (fun y hy => ?_)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [map_zsmul, hf, zsmul_eq_mul, map_mul, map_mul]
    calc v (g (f j) : Ω) * (v (D : Ω) * v (c j)) ≤ 1 * (v (D : Ω) * v (c j)) := by
          gcongr; exact hint _
      _ ≤ v (D : Ω) * v (c i0) := by rw [one_mul]; gcongr; exact hmax' j hj
  rw [map_mul] at hle
  have hle' : v (c i) ≤ v (c i0) := by
    calc v (c i) = (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i)) := (inv_mul_cancel_left₀ hDv _).symm
      _ ≤ (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i0)) := by gcongr
      _ = v (c i0) := inv_mul_cancel_left₀ hDv _
  have hv0 : v (c i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hi0
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc v (c i) * (v (c i0))⁻¹ ≤ v (c i0) * (v (c i0))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hv0

theorem prim_of_bounded : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ a : X.K, a ≠ 0 → (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp a).coeff r)) → ∃ κ : Ω, κ ≠ 0 ∧ Prim A (X.exp (algebraMap Ω X.K κ * a)) ∧ ∃ S : Finset Ω, ∀ r, (X.exp (algebraMap Ω X.K κ * a)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X _ l _ A _ a ha hb
  obtain ⟨S, D, hD, hc⟩ := hb
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hne : ∃ r, (X.exp a).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : X.exp a = 0 := HahnSeries.ext (funext h)
    exact ha ((map_eq_zero_iff X.exp (RingHom.injective X.exp.toRingHom)).1 h0)
  obtain ⟨r0, h0, hA⟩ := exists_dividing A (fun r => (X.exp a).coeff r) _ D hD hc hne
  have hcoef : ∀ (κ : Ω) r, (X.exp (algebraMap Ω X.K κ * a)).coeff r = κ * (X.exp a).coeff r := by
    intro κ r
    rw [map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  refine ⟨((X.exp a).coeff r0)⁻¹, inv_ne_zero h0, ⟨fun r => ?_, r0, ?_⟩, S, fun r => ?_⟩
  · rw [hcoef, mul_comm]; exact hA r
  · rw [hcoef, inv_mul_cancel₀ h0, inv_one]
    exact ⟨one_ne_zero, one_mem A⟩
  · rw [hcoef]
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (hc r0).1) (hc r).1

end GlobalTheory.PrimConst
