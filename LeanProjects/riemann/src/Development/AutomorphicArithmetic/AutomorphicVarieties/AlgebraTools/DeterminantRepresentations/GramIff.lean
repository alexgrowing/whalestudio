import Mathlib

open Polynomial Matrix

private theorem linearIndependent_iff_det_trace_gram_ne_zero {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (v : ι × ι → Matrix ι ι K) :
    LinearIndependent K v ↔ (Matrix.of fun a b => (v a * v b).trace).det ≠ 0 := by
  have hrow : ∀ (c : ι × ι → K) a,
      (v a * ∑ b, c b • v b).trace = ((Matrix.of fun a b => (v a * v b).trace) *ᵥ c) a := by
    intro c a
    rw [Finset.mul_sum, Matrix.trace_sum]
    simp [Matrix.mulVec, dotProduct, Matrix.trace_smul, mul_comm]
  constructor
  · intro hv hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have htop : Submodule.span K (Set.range v) = ⊤ :=
      hv.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_matrix, Fintype.card_prod])
    have hall : ∀ X ∈ Submodule.span K (Set.range v), (X * ∑ b, c b • v b).trace = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [hrow, hc]
        rfl
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
      | smul r x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
    have hY : ∑ b, c b • v b = 0 := by
      ext i j
      have h := hall (Matrix.single j i 1) (htop ▸ Submodule.mem_top)
      rw [Matrix.trace_single_mul, one_smul] at h
      simpa using h
    exact hc0 (funext (Fintype.linearIndependent_iff.1 hv c hY))
  · intro hdet
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    apply hdet
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨c, fun h => hi (congrFun h i), ?_⟩
    funext a
    rw [← hrow, hc, Matrix.mul_zero, Matrix.trace_zero]
    rfl

theorem UpperTheory.V.AlgebraTools.Det.gramIff :
    ∀ {K G ι : Type} [Field K] [Monoid G] [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι K),
    Submodule.span K (Set.range ρ) = ⊤ ↔ ∃ g : ι × ι → G, (Matrix.of fun a b => (ρ (g a * g b)).trace).det ≠ 0 := by
  intro K G ι _ _ _ _ ρ
  have hcard : Fintype.card (ι × ι) = Module.finrank K (Matrix ι ι K) := by
    simp [Module.finrank_matrix, Fintype.card_prod]
  constructor
  · intro hspan
    obtain ⟨s, hsr, hss, hli⟩ := exists_linearIndependent K (Set.range ρ)
    have hs_top : Submodule.span K s = ⊤ := hss.trans hspan
    let bs := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hs_top.ge)
    haveI : Fintype s := (hli.setFinite).fintype
    have hcs : Fintype.card (ι × ι) = Fintype.card s := hcard.trans (Module.finrank_eq_card_basis bs)
    let e : ι × ι ≃ s := Fintype.equivOfCardEq hcs
    have hmem : ∀ a, ∃ y, ρ y = (e a : Matrix ι ι K) := fun a => hsr (e a).2
    refine ⟨fun a => (hmem a).choose, ?_⟩
    have hv : (fun a => ρ (hmem a).choose) = fun a => ((e a : s) : Matrix ι ι K) :=
      funext fun a => (hmem a).choose_spec
    have hvli : LinearIndependent K (fun a => ρ (hmem a).choose) := by
      rw [hv]
      exact hli.comp e e.injective
    simpa only [map_mul] using (linearIndependent_iff_det_trace_gram_ne_zero _).1 hvli
  · rintro ⟨g, hg⟩
    have hvli : LinearIndependent K (fun a => ρ (g a)) :=
      (linearIndependent_iff_det_trace_gram_ne_zero (fun a => ρ (g a))).2 (by simpa only [map_mul] using hg)
    have htop := hvli.span_eq_top_of_card_eq_finrank' hcard
    rw [eq_top_iff, ← htop]
    exact Submodule.span_mono (Set.range_comp_subset_range g ρ)
