import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCut

namespace GlobalTheory.LowerIntegralMul

theorem intLow_mul {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (Mp : Formalism.MainNotions.S.Loc.Model F E) {n : ℕ}
    {l l' : Matrix (Fin n) (Fin n) E} (hl : Formalism.MainNotions.S.TieN.IntLow Mp l) (hl' : Formalism.MainNotions.S.TieN.IntLow Mp l') :
    Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  unfold Formalism.MainNotions.S.TieN.IntLow at *
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [h2' c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge a c with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_le_of_lt h hab), mul_zero]
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (h3 a c) (h3' c b)

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [inst_3 : CommRing E]
    [inst_4 : Algebra F E] [inst_5 : TopologicalSpace E] [inst_6 : MeasurableSpace E] (Mp : Formalism.MainNotions.S.Loc.Model F E)
    {n : ℕ} {l l' : Matrix (Fin n) (Fin n) E},
    Formalism.MainNotions.S.TieN.IntLow Mp l → Formalism.MainNotions.S.TieN.IntLow Mp l' → Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  intro F E _ _ _ _ _ _ _ Mp n l l' hl hl'
  exact intLow_mul Mp hl hl'

end GlobalTheory.LowerIntegralMul
