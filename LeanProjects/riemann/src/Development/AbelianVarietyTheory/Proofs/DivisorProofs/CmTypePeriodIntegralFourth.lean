import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Div.cm_type_period_integral_fourth

theorem exists_smul_mem_of_tmul_mem_baseChange {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {H : Type} [AddCommGroup H] [Module O H] (Fil : Submodule O H) (h : H)
    (hh : (1 : K) ⊗ₜ[O] h ∈ Fil.baseChange K) : ∃ d : O, d ≠ 0 ∧ d • h ∈ Fil := by
  have key : ∀ x ∈ Fil.baseChange K, ∃ s : O, s ≠ 0 ∧ ∃ f ∈ Fil, algebraMap O K s • x = (1 : K) ⊗ₜ[O] f := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      exact ⟨1, one_ne_zero, f, hf, by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, Fil.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨t, ht, g, hg, e'⟩ := ihy
      refine ⟨s * t, mul_ne_zero hs ht, t • f + s • g, Fil.add_mem (Fil.smul_mem _ hf) (Fil.smul_mem _ hg), ?_⟩
      simp only [map_mul, smul_add, mul_smul]
      rw [smul_comm (algebraMap O K s) (algebraMap O K t) x, e, e', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul, algebraMap_smul, algebraMap_smul]
    | smul k x _ ihx =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
      have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
      refine ⟨b * s, mul_ne_zero hb hs, a • f, Fil.smul_mem _ hf, ?_⟩
      rw [← mul_smul, map_mul, mul_assoc, mul_comm (algebraMap O K s), ← mul_assoc,
        mul_comm (algebraMap O K (b : O)), IsLocalization.mk'_spec, mul_smul, e, TensorProduct.tmul_smul,
        algebraMap_smul]
  obtain ⟨s, hs, f, hf, e⟩ := key _ hh
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  have h0 : TensorProduct.mk O K H 1 (s • h - f) = 0 := by
    rw [map_sub, map_smul, TensorProduct.mk_apply, TensorProduct.mk_apply, ← algebraMap_smul K, e, sub_self]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0
  refine ⟨(t : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero t.2) hs, ?_⟩
  have : (t : O) • (s • h) = (t : O) • f := by
    rw [Submonoid.smul_def, smul_sub, sub_eq_zero] at ht
    exact ht
  rw [mul_smul, this]
  exact Fil.smul_mem _ hf

theorem fil_inf_eigLat_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i) := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL i
  refine inf_eq_right.2 fun h hh => ?_
  obtain ⟨-, -, -, -, hsat, hbc, -⟩ := hL
  have h1 : inK K H h ∈ Fil.baseChange K := by
    rw [hbc]
    exact le_iSup (fun j => eigK ρ (φ j)) i hh
  obtain ⟨d, hd, hdh⟩ := exists_smul_mem_of_tmul_mem_baseChange Fil h h1
  exact hsat d h hd hdh

end GlobalTheory.Div.cm_type_period_integral_fourth
