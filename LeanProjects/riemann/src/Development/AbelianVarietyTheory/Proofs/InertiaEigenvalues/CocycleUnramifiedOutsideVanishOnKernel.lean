import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Formalism.GaloisCohomology.Statement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise

namespace GlobalTheory.UnramCocycle

theorem conj_mem_ine_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g σ : G F Ω) (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ

  have hmem : ∀ y : Ω, y ∈ g • A ↔ g⁻¹ y ∈ A := fun y =>
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
  have hgg : ∀ y : Ω, g⁻¹ (g y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine ⟨?_, fun x hx => ?_⟩
  · have h' : σ • (g • A) = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h', inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, hmem, hgg]
      exact (ValuationSubring.valuation_le_one_iff A x).1 hx
    have hy := hval (g x) hx'
    have e : (g⁻¹ * σ * g) x - x = g⁻¹ (σ (g x) - g x) := by
      rw [map_sub, hgg, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    rw [e]
    rw [valuation_lt_one_iff'] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨(hmem _).1 hy1, ?_⟩
    rcases hy2 with h0 | h0
    · left
      rw [h0, map_zero]
    · right
      rwa [← map_inv₀, ← hmem]

def kerSub {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : Subgroup Γ where
  carrier := {n | x.1 n = 0 ∧ ∀ m, ρ n m = m}
  one_mem' := ⟨by simpa using x.2.2 1 1, fun m => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [x.2.2, ha, hb]; simp, fun m => ?_⟩
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    · have h := x.2.2 a a⁻¹
      rw [mul_inv_cancel, h1, ha, ha', zero_add] at h
      exact h.symm
    · conv_lhs => rw [← ha' m]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem kerSub_normal {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : (kerSub ρ x).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨hx, hρ⟩ := hn
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    ·
      rw [x.2.2, x.2.2, hx, map_zero, add_zero, map_mul, Module.End.mul_apply, hρ, ← x.2.2,
        mul_inv_cancel, h1]
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hρ,
        ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem kerSub_isClosed {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (hρ : ContAction ρ) (x : Z1 ρ) :
    IsClosed (kerSub ρ x : Set Γ) := by

  have h1 : IsClosed {n : Γ | x.1 n = 0} := isClosed_eq x.2.1 continuous_const
  have hc : Continuous fun p : Γ × M => ρ p.1 p.2 := hρ
  have h2 : IsClosed {n : Γ | ∀ m, ρ n m = m} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun m =>
      isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  exact h1.inter h2

theorem vanish_on_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ ρ hρ A S htriv x hx
  have := kerSub_normal ρ x

  have hle : NS Ω S ≤ kerSub ρ x := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ (kerSub_isClosed ρ hρ x)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hσ
    obtain ⟨v, hv, B, hB, hσB⟩ := hσ

    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hB
    have hσ' : σ ∈ Ine (F := F) (g • A.1 v) := by rw [hg, mem_Ine]; exact hσB
    have hc := conj_mem_ine_of_smul (A.1 v) g σ hσ'

    have hzero : x.1 (g⁻¹ * σ * g) = 0 := by
      have hu := hx v hv
      unfold Formalism.GaloisCohomology.unrAt H1ur at hu
      rw [LinearMap.mem_ker] at hu
      unfold resH1 at hu
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hu
      obtain ⟨m, hm⟩ := hu
      have hmem : g⁻¹ * σ * g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hc
      have h := hm ⟨⟨g⁻¹ * σ * g, hmem⟩, (Subgroup.mem_subgroupOf).2 hc⟩

      have h' : x.1 (g⁻¹ * σ * g) = ρ (g⁻¹ * σ * g) m - m := h
      rw [htriv v hv (A.1 v) (A.2 v) _ hc, sub_self] at h'
      exact h'
    have hk : g⁻¹ * σ * g ∈ kerSub ρ x := ⟨hzero, htriv v hv (A.1 v) (A.2 v) _ hc⟩
    have h := (kerSub_normal ρ x).conj_mem _ hk g
    have e : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rwa [e] at h
  exact fun n hn => hle hn

end GlobalTheory.UnramCocycle
