import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open Matrix

namespace LateralTheory.CohomologicalPurity.MatPf

theorem gens {d : ℕ} {A : Type} [CommRing A] (x y : Fin d → A)
    (h : Ideal.span (Set.range x) ≤ Ideal.span (Set.range y)) :
    ∃ N : Matrix (Fin d) (Fin d) A, x = N *ᵥ y := by
  have : ∀ i, ∃ c : Fin d → A, ∑ j, c j * y j = x i := fun i =>
    (Ideal.mem_span_range_iff_exists_fun).1 (h (Ideal.subset_span ⟨i, rfl⟩))
  choose c hc using this
  exact ⟨Matrix.of c, funext fun i => by simp [mulVec, dotProduct, hc]⟩

theorem red {d : ℕ} {A : Type} [CommRing A] (x y : Fin d → A) (N N' T : Matrix (Fin d) (Fin d) A)
    (hy : y = N *ᵥ x) (hx : x = N' *ᵥ y) : y = (N + T * (1 - N' * N)) *ᵥ x := by
  have : (1 - N' * N) *ᵥ x = 0 := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← hy, ← hx, sub_self]
  rw [add_mulVec, ← mulVec_mulVec, this, mulVec_zero, add_zero, hy]

theorem glue_dom (hD : ∀ (d : ℕ) (D : Type) [CommRing D] [IsDomain D] (N E N' : Matrix (Fin d) (Fin d) D),
    N' * N + E = 1 → ∃ T : Matrix (Fin d) (Fin d) D, (N + T * E).det ≠ 0) : LateralTheory.CohomologicalPurity.Cl.LeafMat := by
  intro d A _ x y hxy p
  obtain ⟨N, hN⟩ := gens y x hxy.ge
  obtain ⟨N', hN'⟩ := gens x y hxy.le
  let f := Ideal.Quotient.mk p.asIdeal
  obtain ⟨T₀, hT₀⟩ := hD d (A ⧸ p.asIdeal) (f.mapMatrix N) (f.mapMatrix (1 - N' * N)) (f.mapMatrix N')
    (by rw [← map_mul, ← map_add, add_sub_cancel, map_one])
  choose T hT using fun i j => Ideal.Quotient.mk_surjective (I := p.asIdeal) (T₀ i j)
  refine ⟨N + Matrix.of T * (1 - N' * N), ?_, red x y N N' _ hN hN'⟩
  intro hm
  apply hT₀
  have h1 : f.mapMatrix (Matrix.of T) = T₀ := by ext i j; simp [f, hT]
  have := RingHom.map_det f (N + Matrix.of T * (1 - N' * N))
  rw [map_add, map_mul, h1, (Ideal.Quotient.eq_zero_iff_mem).2 hm] at this
  exact this.symm

theorem fld {d : ℕ} {k : Type} [Field k] (N E N' : Matrix (Fin d) (Fin d) k) (h : N' * N + E = 1) :
    ∃ T : Matrix (Fin d) (Fin d) k, ∀ s : k, s ≠ 0 → (N + (s • T) * E).det ≠ 0 := by
  classical
  let n := Matrix.toLin' N
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range n)
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker n)
  have hr : Module.finrank k (LinearMap.ker n) = Module.finrank k C := by
    have h1 := LinearMap.finrank_range_add_finrank_ker n
    have h2 := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hr
  let t : (Fin d → k) →ₗ[k] (Fin d → k) :=
    C.subtype ∘ₗ e.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl _ _ hK
  refine ⟨LinearMap.toMatrix' t, fun s hs hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  apply hv0
  have hE : E = 1 - N' * N := by rw [← h]; abel
  rw [add_mulVec, ← mulVec_mulVec, smul_mulVec, LinearMap.toMatrix'_mulVec] at hv
  have htC : ∀ w, t w ∈ C := fun w => (e _).2
  have hnv : n v = 0 := by
    have hm : n v ∈ C := by
      have : n v = -(s • t (E *ᵥ v)) := eq_neg_of_add_eq_zero_left (by simpa [n] using hv)
      rw [this]; exact C.neg_mem (C.smul_mem s (htC _))
    exact (Submodule.disjoint_def.1 hC.disjoint) _ (LinearMap.mem_range_self n v) hm
  have hNv : N *ᵥ v = 0 := by simpa [n] using hnv
  have hw : E *ᵥ v = v := by
    rw [hE, sub_mulVec, one_mulVec, ← mulVec_mulVec, hNv, mulVec_zero, sub_zero]
  rw [hw, hNv, zero_add, smul_eq_zero] at hv
  have htv : t v = 0 := hv.resolve_left hs
  have hker : v ∈ LinearMap.ker n := hnv
  have hp : Submodule.linearProjOfIsCompl _ _ hK v = ⟨v, hker⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hker⟩
  have : e ⟨v, hker⟩ = 0 := by
    apply Subtype.ext
    have := htv
    simp only [t, LinearMap.comp_apply, hp] at this
    simpa using this
  have := congrArg Subtype.val (e.map_eq_zero_iff.1 this)
  simpa using this

theorem dom (d : ℕ) (D : Type) [CommRing D] [IsDomain D] (N E N' : Matrix (Fin d) (Fin d) D)
    (h : N' * N + E = 1) : ∃ T : Matrix (Fin d) (Fin d) D, (N + T * E).det ≠ 0 := by
  classical
  let g := algebraMap D (FractionRing D)
  obtain ⟨T, hT⟩ := fld (g.mapMatrix N) (g.mapMatrix E) (g.mapMatrix N')
    (by rw [← map_mul, ← map_add, h, map_one])
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D)
    (fun ij : Fin d × Fin d => T ij.1 ij.2)
  choose T' hT' using fun i j => hb (i, j)
  have h1 : g.mapMatrix (Matrix.of T') = g b • T := by
    ext i j; simp [g, hT', Algebra.smul_def]
  have hne : g b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Matrix.of T', fun h0 => hT (g b) hne ?_⟩
  have := RingHom.map_det g (N + Matrix.of T' * E)
  rw [h0, map_zero, map_add, map_mul, h1] at this
  exact this.symm

end LateralTheory.CohomologicalPurity.MatPf

theorem LateralTheory.CohomologicalPurity.Cl.LeafMat_of : LateralTheory.CohomologicalPurity.Cl.LeafMat := LateralTheory.CohomologicalPurity.MatPf.glue_dom LateralTheory.CohomologicalPurity.MatPf.dom
