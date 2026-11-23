import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegralStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem apply_of_mem_eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {x : V}
    (hx : x ∈ eigSp ρ σ) (a : 𝓞 E) : ρ a x = σ (a : E) • x := by
  have := (Submodule.mem_iInf _).1 hx a
  simpa [sub_eq_zero] using this

theorem sum_smul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {N : ℕ} (t : Fin N → V)
    (y : Fin N → K) :
    ∑ i, y i • eigProj ρ σ (t i) =
      ∑ q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
        (y q.1 * σ (dualInt E q.2)) • ρ (RingOfIntegers.basis E q.2) (t q.1) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eigProj, LinearMap.sum_apply, Finset.smul_sum, mul_smul]

omit [Algebra A K] [IsScalarTower A K V] in
theorem mem_of_isFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V)
    (h : IsFreeOn ρ X t) (i : Fin N) : t i ∈ X := by
  have h1 : t i = ∑ k, (RingOfIntegers.basis E).repr 1 k • ρ (RingOfIntegers.basis E k) (t i) := by
    have := congrArg (fun a => ρ a (t i)) ((RingOfIntegers.basis E).sum_repr 1)
    simp only [map_sum, map_zsmul, map_one, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    exact this.symm
  rw [h1, h.2.2]
  refine Submodule.sum_mem _ fun k _ => ?_
  refine zsmul_mem ?_ _
  exact Submodule.subset_span ⟨(i, k), rfl⟩

theorem eigSub_eq_different_smul_eigQuot : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) (N : ℕ) (t : Fin N → V) (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → IsFreeOn ρ X t → (∀ x, x ∈ eigQuot ρ σ X ↔ d • x ∈ eigSub ρ σ X) ∧ eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) ∧ LinearIndependent K (fun i => eigProj ρ σ (t i)) ∧ Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
  intro A K _ _ _ _ V _ _ _ _ E _ _ ρ X N t σ d hinj hσ hd hX
  obtain ⟨he1, he2, -, he4⟩ := ProjEig.eigProj_spec K V E ρ σ
  obtain ⟨hd0, hd1, u, hu⟩ := GlobalTheory.T.different_generator_dual_integral A K E σ d hinj hσ hd
  have hQ : eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) := by
    apply le_antisymm
    · unfold eigQuot
      rw [hX.2.2, Submodule.map_span_le]
      rintro _ ⟨⟨i, k⟩, rfl⟩
      obtain ⟨a, ha⟩ := hσ (RingOfIntegers.basis E k)
      have : eigProj ρ σ (ρ (RingOfIntegers.basis E k) (t i)) = a • eigProj ρ σ (t i) := by
        rw [← Module.End.mul_apply, he4, Module.End.mul_apply,
          apply_of_mem_eigSp ρ σ (he1 _), ← ha, IsScalarTower.algebraMap_smul]
      simp only [LinearMap.restrictScalars_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, mem_of_isFreeOn ρ X t hX i, rfl⟩
  have hli : LinearIndependent K (fun i => eigProj ρ σ (t i)) := by
    rw [Fintype.linearIndependent_iff]
    intro y hy i
    rw [sum_smul_eigProj] at hy
    have h0 := Fintype.linearIndependent_iff.1 hX.1 _ hy
    calc y i = y i * ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) := by
          rw [hu, mul_one]
      _ = ∑ k, algebraMap A K (u k) * algebraMap A K d * (y i * σ (dualInt E k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          have := h0 (i, k)
          simp only at this
          rw [this, mul_zero]
  have hsp : Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he1 _
    · intro x hx
      rw [← he2 x hx]
      have hx' : x ∈ Submodule.span K (X : Set V) := by rw [hX.2.1]; trivial
      have : (Submodule.span K (X : Set V)).map (eigProj ρ σ) ≤
          Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) := by
        rw [Submodule.map_span_le]
        intro m hm
        apply Submodule.span_le_restrictScalars A K
        rw [← hQ]
        exact ⟨m, hm, rfl⟩
      exact this ⟨x, hx', rfl⟩
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hQ, hli, hsp⟩
  · refine ⟨?_, ?_⟩
    · rw [hQ, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, rfl⟩ := hx
      have : d • ∑ i, c i • eigProj ρ σ (t i) =
          ∑ i, (algebraMap A K (c i) * algebraMap A K d) • eigProj ρ σ (t i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_mul, IsScalarTower.algebraMap_smul, mul_comm, mul_smul]
      rw [this, sum_smul_eigProj, hX.2.2]
      refine Submodule.sum_mem _ fun q _ => ?_
      obtain ⟨a, ha⟩ := hd1 q.2
      rw [mul_assoc, ← ha, ← map_mul, IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    · obtain ⟨m, -, rfl⟩ := hx
      exact Submodule.smul_mem _ d (show _ ∈ (eigSp ρ σ).restrictScalars A from he1 m)
  · obtain ⟨hx1, hx2⟩ := hx
    have hxe : x ∈ eigSp ρ σ := by
      have h2 : algebraMap A K d • x ∈ eigSp ρ σ := by
        rw [IsScalarTower.algebraMap_smul]; exact hx2
      exact (Submodule.smul_mem_iff _ hd0).1 h2
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hxe
    obtain ⟨y, rfl⟩ := hxe
    have hx1' : d • ∑ i, y i • eigProj ρ σ (t i) ∈ X := hx1
    rw [hX.2.2, Submodule.mem_span_range_iff_exists_fun] at hx1'
    obtain ⟨c, hc⟩ := hx1'
    have h3 : d • ∑ i, y i • eigProj ρ σ (t i) =
        ∑ i, (y i * algebraMap A K d) • eigProj ρ σ (t i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, IsScalarTower.algebraMap_smul]
    rw [h3, sum_smul_eigProj] at hc
    have h4 : ∀ q, algebraMap A K (c q) = y q.1 * algebraMap A K d * σ (dualInt E q.2) := by
      refine Fintype.linearIndependent_iffₛ.1 hX.1 _ _ ?_
      rw [← hc]
      exact Finset.sum_congr rfl fun q _ => IsScalarTower.algebraMap_smul _ _ _
    rw [hQ]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h5 : y i = algebraMap A K (∑ k, u k * c (i, k)) := by
      rw [map_sum, ← mul_one (y i), ← hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, h4]
      ring
    rw [h5, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot
