import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
open MeasureTheory Filter Topology

namespace GlobalTheory.ThK.Dbl.Contin

theorem exists_finset_separating {M I : Type} [AddCommGroup M] [Module ℂ M]
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (ev : I → M →ₗ[ℂ] ℂ)
    (hsep : ∀ v ∈ V, (∀ i, ev i v = 0) → v = 0) :
    ∃ P : Finset I, ∀ v ∈ V, (∀ i ∈ P, ev i v = 0) → v = 0 := by
  classical
  let K : Finset I → Submodule ℂ V := fun P => ⨅ i ∈ P, LinearMap.ker ((ev i).comp V.subtype)
  have hK : ∀ P (v : V), v ∈ K P ↔ ∀ i ∈ P, ev i v = 0 := by
    intro P v; simp [K, Submodule.mem_iInf]
  obtain ⟨W, ⟨P, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule ℂ V))
    (Set.range K) ⟨K ∅, ∅, rfl⟩
  refine ⟨P, fun v hv h0 => ?_⟩
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, ev i v ≠ 0 := by
    by_contra h; push_neg at h; exact hne (hsep v hv h)
  refine hmin (K (insert i P)) ⟨_, rfl⟩ (lt_of_le_of_ne ?_ ?_)
  · intro w hw; rw [hK] at hw ⊢; intro j hj; exact hw j (Finset.mem_insert_of_mem hj)
  · intro heq
    have : (⟨v, hv⟩ : V) ∈ K P := (hK P _).2 h0
    rw [← heq, hK] at this
    exact hi (this i (Finset.mem_insert_self _ _))

theorem inSpan_iff_mem_span {G : Type} [Mul G] (f f' w w' : G → ℂ) :
    InSpan f f' w w' ↔ (w, w') ∈ Submodule.span ℂ
      (Set.range fun y : G => ((fun h => f (h * y)), (fun h => f' (h * y)))) := by
  classical
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨n, y, c, rfl, rfl⟩
    refine ⟨n, c, fun j => ⟨_, y j, rfl⟩, ?_⟩
    ext h <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · rintro ⟨n, c, g, hg⟩
    choose y hy using fun j => (g j).2
    refine ⟨n, y, c, ?_, ?_⟩
    · have : w = (∑ i, c i • (g i : (G → ℂ) × (G → ℂ))).1 := by rw [hg]
      rw [this]; ext h
      simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hy j]
    · have : w' = (∑ i, c i • (g i : (G → ℂ) × (G → ℂ))).2 := by rw [hg]
      rw [this]; ext h
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hy j]

end GlobalTheory.ThK.Dbl.Contin

namespace GlobalTheory.ThK.Dbl.Contin

theorem main : ∀ {G : Type} [Group G] (Ω Ω₁ : Set ℂ) (s₀ : ℂ) (W₀ : Submodule ℂ (G → ℂ)) (f f' : G → ℂ) (u u' : ℂ → G → ℂ),
    IsOpen Ω → IsPreconnected Ω → s₀ ∈ Ω → IsOpen Ω₁ → Ω₁.Nonempty → Ω₁ ⊆ Ω → FiniteDimensional ℂ W₀ →
    (∀ h, DifferentiableOn ℂ (fun s => u s h) Ω) → (∀ h, DifferentiableOn ℂ (fun s => u' s h) Ω) →
    (∀ s ∈ Ω, u s ∈ W₀ ∧ u' s ∈ W₀) → (∀ s ∈ Ω₁, GlobalTheory.ThK.Dbl.InSpan f f' (u s) (u' s)) →
    GlobalTheory.ThK.Dbl.InSpan f f' (u s₀) (u' s₀) := by
  intro G _ Ω Ω₁ s₀ W₀ f f' u u' hΩ hconn hs₀ hΩ₁ hne hsub hfin hu hu' hW hspan
  classical
  set D : Submodule ℂ ((G → ℂ) × (G → ℂ)) := Submodule.span ℂ
      (Set.range fun y : G => ((fun h => f (h * y)), (fun h => f' (h * y)))) with hDdef
  have hD : ∀ w w', InSpan f f' w w' ↔ (w, w') ∈ D := fun w w' => inSpan_iff_mem_span f f' w w'
  set V : Submodule ℂ ((G → ℂ) × (G → ℂ)) := W₀.prod W₀ with hVdef
  have hVr : LinearMap.range (W₀.subtype.prodMap W₀.subtype) = V := by
    rw [LinearMap.range_prodMap, Submodule.range_subtype]
  haveI : FiniteDimensional ℂ V := LinearEquiv.finiteDimensional (LinearEquiv.ofEq _ _ hVr)
  let ev : G ⊕ G → ((G → ℂ) × (G → ℂ)) →ₗ[ℂ] ℂ := Sum.elim
    (fun h => (LinearMap.proj h) ∘ₗ LinearMap.fst ℂ _ _) (fun h => (LinearMap.proj h) ∘ₗ LinearMap.snd ℂ _ _)
  have hsep : ∀ v ∈ V, (∀ i, ev i v = 0) → v = 0 := by
    intro v _ h0
    ext x
    · simpa [ev] using h0 (Sum.inl x)
    · simpa [ev] using h0 (Sum.inr x)
  obtain ⟨P, hP⟩ := exists_finset_separating V ev hsep
  let T : ((G → ℂ) × (G → ℂ)) →ₗ[ℂ] (P → ℂ) := LinearMap.pi fun i => ev i
  have hT : ∀ p i, T p i = ev i p := fun p i => rfl
  let S' : Submodule ℂ (P → ℂ) := (D ⊓ V).map T
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S'
  let q : (P → ℂ) →ₗ[ℂ] C := Submodule.projectionOnto C S' hC.symm
  have hq : ∀ x, q x = 0 ↔ x ∈ S' := by
    intro x
    rw [← LinearMap.mem_ker]
    show x ∈ LinearMap.ker (Submodule.projectionOnto C S' hC.symm) ↔ _
    rw [Submodule.ker_projectionOnto]
  let Lc : (P → ℂ) →L[ℂ] (P → ℂ) := LinearMap.toContinuousLinearMap (C.subtype ∘ₗ q)
  let F : ℂ → (P → ℂ) := fun s => Lc (T (u s, u' s))
  have hΦ : DifferentiableOn ℂ (fun s => T (u s, u' s)) Ω := by
    rw [differentiableOn_pi]
    intro i
    rcases i with ⟨i | i, _⟩
    · simpa [hT, ev] using hu i
    · simpa [hT, ev] using hu' i
  have hF : DifferentiableOn ℂ F Ω := fun s hs =>
    Lc.differentiableAt.comp_differentiableWithinAt s (hΦ s hs)
  have hF0 : ∀ s ∈ Ω₁, F s = 0 := by
    intro s hs
    have hmem : T (u s, u' s) ∈ S' :=
      Submodule.mem_map_of_mem ⟨(hD _ _).1 (hspan s hs), hW s (hsub hs)⟩
    simp only [F, Lc, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype]
    rw [(hq _).2 hmem]; rfl
  obtain ⟨z₀, hz₀⟩ := hne
  have hev : F =ᶠ[𝓝 z₀] 0 :=
    Filter.eventually_of_mem (hΩ₁.mem_nhds hz₀) fun s hs => hF0 s hs
  have hEq := (hF.analyticOnNhd hΩ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
    (hsub hz₀) hev
  have hFs₀ : F s₀ = 0 := hEq hs₀
  have hmem : T (u s₀, u' s₀) ∈ S' := by
    rw [← hq]
    simp only [F, Lc, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype] at hFs₀
    exact Subtype.ext hFs₀
  obtain ⟨k, ⟨hkD, hkV⟩, hk⟩ := Submodule.mem_map.1 hmem
  have hdiff : (u s₀, u' s₀) - k = 0 := by
    apply hP _ (V.sub_mem ⟨(hW s₀ hs₀).1, (hW s₀ hs₀).2⟩ hkV)
    intro i hi
    have := congrFun hk ⟨i, hi⟩
    rw [hT, hT] at this
    rw [map_sub, ← this, sub_self]
  rw [sub_eq_zero] at hdiff
  rw [hD, hdiff]; exact hkD

end GlobalTheory.ThK.Dbl.Contin
