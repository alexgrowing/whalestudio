import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.lift_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (w : ι → X) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) (c : Γ → ι → ι → O),
      (∀ g a b, residue O (c g a b) = rbar g a b) → (∀ g a b, w a ≠ w b → c g a b = 0) → r.Generates → r.TStable w →
      ∃ W : WPres O X R, (∀ g a b, r.hom g a b ∈ W.part (w a - w b)) ∧
        ∀ i, ∃ g a b, W.z i = r.hom g a b - algebraMap O R (c g a b) ∧ W.wt i = w a - w b := by
  intro O _ _ _ _ X _ _ _ Γ ι _ _ _ _ rbar w R _ _ _ r c hc hc0 hgen hst
  obtain ⟨W, u, hu, he⟩ := UpperTheory.V.Alg.coord_grading O X R (Γ × ι × ι)
    (fun s => r.hom s.1 s.2.1 s.2.2 - algebraMap O R (c s.1 s.2.1 s.2.2)) (fun s => w s.2.1 - w s.2.2)
    (fun s => by
      rw [← res_eq_zero_iff O, map_sub, r.red, AlgHom.commutes, ← hc, sub_eq_zero]
      rfl)
    (fun R' _ _ _ f f' h => hgen R' f f' (by
      ext g a b
      have := h (g, a, b)
      simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
      exact this))
    (fun R' _ _ _ f t ht => by
      obtain ⟨f', hf'⟩ := hst R' f t ht
      refine ⟨f', fun ⟨g, a, b⟩ => ?_⟩
      have h1 : f' (r.hom g a b) = t (Multiplicative.ofAdd (w a - w b)) * f (r.hom g a b) := hf' g a b
      show f' (r.hom g a b - algebraMap O R (c g a b)) =
        t (Multiplicative.ofAdd (w a - w b)) * f (r.hom g a b - algebraMap O R (c g a b))
      rw [map_sub f', map_sub f, AlgHom.commutes, AlgHom.commutes, h1, mul_sub]
      by_cases hab : w a = w b
      · simp [hab]
      · simp [hc0 g a b hab])
  refine ⟨W, fun g a b => ?_, fun i => ⟨(u i).1, (u i).2.1, (u i).2.2, (hu i).1, (hu i).2⟩⟩
  have h1 : r.hom g a b - algebraMap O R (c g a b) ∈ W.part (w a - w b) := he (g, a, b)
  have h2 : algebraMap O R (c g a b) ∈ W.part (w a - w b) := by
    by_cases hab : w a = w b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    · rw [hc0 g a b hab, map_zero]
      exact zero_mem _
  simpa using add_mem h1 h2
