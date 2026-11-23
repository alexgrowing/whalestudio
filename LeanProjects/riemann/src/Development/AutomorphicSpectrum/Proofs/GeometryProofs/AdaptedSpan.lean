import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

section

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem comp_act (𝓗 : HodgeLat L ρ bar r) {σ : E →+* Ω} {φ : Module.Dual Ω V}
    (h : ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ) (a : 𝓞 E) : φ ∘ₗ ρ (bar a) = σ (a : E) • φ := by
  have h1 := (HT.LatBasic.mem_eigSp.mp h) a
  rw [𝓗.act_inr] at h1
  exact congrArg Prod.snd h1

theorem comp_eigProj (𝓗 : HodgeLat L ρ bar r) {σ σ' : E →+* Ω}
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hb : ∀ a, bar (bar a) = a) {φ : Module.Dual Ω V}
    (h : ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ) : φ ∘ₗ HT.eigProj ρ σ' = φ := by
  have key : ∀ b : 𝓞 E, φ ∘ₗ ρ b = σ' (b : E) • φ := by
    intro b
    have h1 := comp_act 𝓗 h (bar b)
    rw [hb b] at h1
    rw [h1, hσ b]
  have hsum : ∑ k, σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    have h1 := congrArg σ' (HT.LatBasic.sum_dualInt_mul (E := E))
    rw [map_sum, map_one] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, NumberField.integralBasis_apply]
  unfold HT.eigProj
  ext x
  have hk : ∀ k, φ ((σ' (HT.dualInt E k) • ρ (RingOfIntegers.basis E k)) x) =
      σ' (HT.dualInt E k) * σ' ((RingOfIntegers.basis E k : 𝓞 E) : E) * φ x := by
    intro k
    have e := LinearMap.congr_fun (key (RingOfIntegers.basis E k)) x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e
    rw [LinearMap.smul_apply, map_smul, e, smul_eq_mul, mul_assoc]
  rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  simp_rw [hk]
  rw [← Finset.sum_mul, hsum, one_mul]

end

theorem adapted_span : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω]
    (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
    (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q r : ℕ) (𝓗 : HodgeLat L ρ bar r)
    (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V),
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v →
    Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w →
    Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u →
    LinearIndependent Ω u ∧ Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ ∧
      ∀ φ : Module.Dual Ω V, ((0 : V), φ) ∈ HT.eigSp 𝓗.ρH σ → φ ∘ₗ HT.eigProj ρ σ' = φ := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q r 𝓗 σ σ' v w u hσ hb hv hvs hw hws hu
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hz : ∀ j, (u (Fin.natAdd p j)).1 = 0 := fun j => (hu3 j).1
  have hz2 : ∀ j j', (u (Fin.natAdd p j)).2 (w j') = if j = j' then 1 else 0 := fun j => (hu3 j).2
  have hli : LinearIndependent Ω u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    have h1 : ∀ i, g (Fin.castAdd q i) = 0 := by
      have hf := congrArg Prod.fst hg
      simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hu2, hz] at hf
      exact Fintype.linearIndependent_iff.mp hv _ hf
    have h2 : ∀ j, g (Fin.natAdd p j) = 0 := by
      intro j'
      have hs := congrArg (fun y : V × Module.Dual Ω V => y.2 (w j')) hg
      simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, h1, hz2] using hs
    intro i
    exact Fin.addCases h1 h2 i
  have hspan : Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hu1 i
    · intro y hy
      have hy1 : y.1 ∈ HT.eigSp ρ σ := by
        rw [HT.LatBasic.mem_eigSp]
        intro a
        have h1 := congrArg Prod.fst ((HT.LatBasic.mem_eigSp.mp hy) a)
        rw [𝓗.act_fst] at h1
        exact h1
      rw [← hvs, Submodule.mem_span_range_iff_exists_fun] at hy1
      obtain ⟨c, hc⟩ := hy1
      set y' := y - ∑ i, c i • u (Fin.castAdd q i) with hy'
      have hy'mem : y' ∈ HT.eigSp 𝓗.ρH σ :=
        Submodule.sub_mem _ hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hu1 _))
      have hy'1 : y'.1 = 0 := by
        simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy', hu2, hc]
      set χ := y'.2 - ∑ j, y'.2 (w j) • (u (Fin.natAdd p j)).2 with hχ
      have hχmem : ((0 : V), χ) ∈ HT.eigSp 𝓗.ρH σ := by
        have e : ((0 : V), χ) = y' - ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
          refine Prod.ext ?_ ?_
          · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy'1, hz]
          · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hχ]
        rw [e]
        exact Submodule.sub_mem _ hy'mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu1 _))
      have hχw : ∀ j', χ (w j') = 0 := by
        intro j'
        simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hχ, hz2]
      have hχker : HT.eigSp ρ σ' ≤ LinearMap.ker χ := by
        rw [← hws, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hχw j
      have hχ0 : χ = 0 := by
        have h2 := comp_eigProj 𝓗 hσ hb hχmem
        ext x
        rw [← h2, LinearMap.comp_apply, LinearMap.zero_apply]
        exact LinearMap.mem_ker.mp (hχker (HT.LatBasic.eigProj_mem ρ σ' x))
      have hy2 : y'.2 = ∑ j, y'.2 (w j) • (u (Fin.natAdd p j)).2 := sub_eq_zero.mp hχ0
      have hT : y' = ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, hy'1, hz]
        · simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] using hy2
      have hyeq : y = ∑ i, c i • u (Fin.castAdd q i) + ∑ j, y'.2 (w j) • u (Fin.natAdd p j) := by
        rw [← hT, hy']
        abel
      rw [hyeq]
      exact Submodule.add_mem _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  exact ⟨hli, hspan, fun φ hφ => comp_eigProj 𝓗 hσ hb hφ⟩

end GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan
