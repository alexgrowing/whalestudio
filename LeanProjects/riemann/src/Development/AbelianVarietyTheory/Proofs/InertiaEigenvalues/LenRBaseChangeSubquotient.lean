import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal

open scoped TensorProduct

namespace GlobalTheory

section

variable {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
  {W : Type} [AddCommGroup W] [Module O W]

theorem isLatIn_baseChange [IsDomain O'] (hinj : Function.Injective (algebraMap O O'))
    {V L : Submodule O W} (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L.baseChange O') (V.baseChange O') := by
  obtain ⟨hfg, hle, hsat⟩ := h
  refine ⟨?_, Submodule.baseChange_mono O' hle, ?_⟩
  · obtain ⟨s, rfl⟩ := hfg
    rw [Submodule.baseChange_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨c, hc, hcv⟩ := hsat v hv
      refine ⟨algebraMap O O' c, fun h0 => hc (hinj (by rw [h0, map_zero])), ?_⟩
      rw [algebraMap_smul, ← map_smul]
      exact Submodule.tmul_mem_baseChange_of_mem 1 hcv
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hay
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hbz
    | smul a y _ hy =>
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨b, hb, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_mem _ _ hby

variable [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
  [IsLocalHom (algebraMap O O')]

theorem lenR_baseChange_subquotient (hinj : Function.Injective (algebraMap O O')) (l : ℕ)
    (A B : Submodule O W) :
    Formalism.MainNotions.IntegralHeckeForms.lenR O' l
              (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Formalism.MainNotions.IntegralHeckeForms.lenR O l (A ⧸ B.comap A.subtype) := by
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  have h1 : Module.length O'
      (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Module.length O (A ⧸ B.comap A.subtype) *
        (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℕ∞) :=
    length_baseChange_subquotient_dvr O O' A B
  have h2 := addVal_algebraMap (R := O) O' (l : O)
  rw [map_natCast] at h2
  have he : (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ramificationIdx_maximalIdeal_pos O O').ne'
  unfold Formalism.MainNotions.IntegralHeckeForms.lenR
  rw [h1, h2, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ he]

end

theorem sIdx_baseChange :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (W : Type) [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ : Submodule O W), Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L₁.baseChange O') (V.baseChange O') ∧ Formalism.MainNotions.IntegralHeckeForms.sIdx l (L₁.baseChange O') (L₂.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ := by
  intro O _ _ _ O' _ _ _ _ _ hinj W _ _ l V L₁ L₂ h₁ _
  refine ⟨isLatIn_baseChange O' hinj h₁, ?_⟩
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx
  rw [lenR_baseChange_subquotient O' hinj, lenR_baseChange_subquotient O' hinj]

end GlobalTheory
