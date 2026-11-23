import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FarReg

theorem highest_preimage_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (T : Submodule ℂ E) (a b : ι → Module.End ℂ E) (D : Module.End ℂ E) (y : E)
    (hT : FiniteDimensional ℂ T)
    (hadj : ∀ i x z, ⟪a i x, z⟫_ℂ = ⟪x, b i z⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) :
    ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  classical
  let S : Submodule ℂ E := Submodule.span ℂ {z | ∃ i, ∃ t ∈ T, z = b i t}
  have hST : S ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, t, ht, rfl⟩
    exact hbT i t ht
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hST
  obtain ⟨u, huS, w, hw, hyuw⟩ := S.exists_add_mem_mem_orthogonal y
  have hbS : ∀ i, ∀ t ∈ T, b i t ∈ S := fun i t ht => Submodule.subset_span ⟨i, t, ht, rfl⟩
  have huT : u ∈ T := hST huS
  have hwT : w ∈ T := by
    have : w = y - u := by rw [hyuw]; abel
    rw [this]
    exact T.sub_mem hy huT
  have haw : ∀ i, a i w = 0 := by
    intro i
    have h0 : ⟪a i w, a i w⟫_ℂ = 0 := by
      rw [hadj]
      exact (Submodule.mem_orthogonal' S w).1 hw _ (hbS i _ (haT i w hwT))
    exact inner_self_eq_zero.1 h0
  have har : ∀ i, a i (D u) = 0 := by
    intro i
    have h1 : a i (D y) = a i (D u) + D (a i w) := by
      rw [← haD i w hwT, ← map_add, ← map_add, hyuw]
    rw [hDy i, haw i, map_zero, add_zero] at h1
    exact h1.symm
  have hperp : ∀ z ∈ S, ⟪D u, D z⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, t, ht, rfl⟩ := hz
      rw [← hbD i t ht, ← hadj, har i, inner_zero_left]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add, inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [map_smul, inner_smul_right, hx, mul_zero]
  have hDu : D u = 0 := inner_self_eq_zero.1 (hperp u huS)
  exact ⟨w, hwT, haw, by rw [hyuw, map_add, hDu, zero_add]⟩

theorem highest_preimage_of_stable : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ι : Type) (T : Submodule ℂ (Cn n V))
    (a b : ι → Module.End ℂ (Cn n V)) (D : Module.End ℂ (Cn n V)) (y : Cn n V), FiniteDimensional ℂ T →
    (∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ) →
    (∀ i, ∀ t ∈ T, a i t ∈ T) → (∀ i, ∀ t ∈ T, b i t ∈ T) →
    (∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) → (∀ i, ∀ t ∈ T, b i (D t) = D (b i t)) →
    y ∈ T → (∀ i, a i (D y) = 0) → ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  intro n V _ _ ι T a b D y hT hadj haT hbT haD hbD hy hDy
  let e : Cn n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Pos n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Pos n) → V)).symm
  let c : Module.End ℂ (Cn n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Pos n) => V)) := fun f =>
    (e : Cn n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cn n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

end GlobalTheory.CompanionTheory.FarReg
