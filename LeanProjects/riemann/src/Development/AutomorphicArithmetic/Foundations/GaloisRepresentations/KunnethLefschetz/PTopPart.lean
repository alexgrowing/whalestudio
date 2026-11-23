import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

theorem topPart_holds : TopPart := by
  intro l _ k _ _ hl d X p hp hR hLow hKun lam s a hlam Λ hΛ δ
  classical
  have hmem : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [hKun.span]
    trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', b', h', u, v, rfl⟩ := hx
    rcases lt_trichotomy b' 0 with hb | hb | hb
    · haveI := hLow.neg X b' hb
      obtain rfl : v = 0 := Subsingleton.elim _ _
      refine ⟨0, ?_, ?_⟩
      · simp [ext2]
      · simp [ext2]
    · subst hb
      obtain rfl : a' = 2 * (d : ℤ) := by omega
      let F : V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] V l (pullback p p) (2 * (d : ℤ)) :=
        (cupV l (pullback p p) h').flip (pb l (pullback.snd p p) 0 v) ∘ₗ
          pb l (pullback.fst p p) (2 * (d : ℤ))
      have hsum : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v) =
          ext2 l p h' u v := by
        calc ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v)
            = ∑ t, a.repr u t • F (a t) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              simp only [ext2, F, map_smul, LinearMap.comp_apply, LinearMap.flip_apply]
          _ = F (∑ t, a.repr u t • a t) := by
              rw [map_sum]
              simp only [map_smul]
          _ = ext2 l p h' u v := by
              rw [a.sum_repr]
              rfl
      refine ⟨fun t => a.repr u t • v, ?_, ?_⟩
      · rw [hΛ.1 u v, ← Finset.sum_smul]
        congr 1
        conv_rhs => rw [← a.sum_repr u]
        rw [map_sum]
        simp only [map_smul, hlam, smul_eq_mul, mul_one]
      · rw [hsum, sub_self]
        exact Submodule.zero_mem _
    · refine ⟨0, ?_, ?_⟩
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact (hΛ.2 a' b' h' (ne_of_gt hb) u v).symm
      · have h0 : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) ((0 : Fin s → V l X 0) t) = 0 := by
          simp [ext2]
        rw [h0, sub_zero]
        rcases le_or_gt 0 a' with ha | ha
        · exact Submodule.subset_span ⟨a', b', h', u, v, ha, hb, rfl⟩
        · haveI := hLow.neg X a' ha
          obtain rfl : u = 0 := Subsingleton.elim _ _
          simp [ext2]
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [ext2]
  | add x y _ _ hx hy =>
    obtain ⟨b1, hb1, hm1⟩ := hx
    obtain ⟨b2, hb2, hm2⟩ := hy
    refine ⟨b1 + b2, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hb1, hb2]
    · convert Submodule.add_mem _ hm1 hm2 using 1
      simp only [ext2, Pi.add_apply, map_add, Finset.sum_add_distrib]
      abel
  | smul c x _ hx =>
    obtain ⟨b, hb, hm⟩ := hx
    refine ⟨c • b, ?_, ?_⟩
    · simp [← Finset.smul_sum, hb]
    · convert Submodule.smul_mem _ c hm using 1
      simp only [ext2, Pi.smul_apply, map_smul, smul_sub, Finset.smul_sum]

end UpperTheory.Gal.KunnethLefschetz
