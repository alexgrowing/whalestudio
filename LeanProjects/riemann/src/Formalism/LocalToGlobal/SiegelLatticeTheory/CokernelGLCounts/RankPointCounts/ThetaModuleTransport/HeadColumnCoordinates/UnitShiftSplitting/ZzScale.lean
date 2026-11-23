import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ScaleCh

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

include hs in
theorem zz_scale (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (u : F) (hu0 : u ≠ 0) (δ₁ δ₂ cc : M.R) (α : E) (he1 : g.e (δ₁ : E) = (u, 1))
    (he2 : g.e (δ₂ : E) = (1, u⁻¹)) (hcc : g.e (cc : E) = ((1 - u) * T / (g.q : F), (1 - u) * T' / (g.q : F)))
    (hα : g.e α = (u, u⁻¹)) :
    (dlast r δ₂ * (Z * dlast r δ₁ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then cc else 0)).map
        M.R.subtype = HermSp.ZZplusOf M (Zh * dlast r α) T T' := by
  ext a b
  have hZab : ((Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := by
    rw [← hZ]; rfl
  have hq : ((g.q : F)) ≠ 0 := by
    intro h
    exact g.q_irr.ne_zero (Subtype.ext h)
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply] at hZab
  simp only [HermSp.ZZplusOf, hs, Matrix.map_apply, Matrix.of_apply, dlast, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.add_apply, Subring.coe_subtype]
  apply g.e.injective
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha; subst hb
    simp only [and_self, if_true] at hZab ⊢
    push_cast
    rw [map_sub, map_mul, map_add, map_mul, hZab]
    simp only [map_sub, AlgEquiv.apply_symm_apply, he1, he2, hcc, hα, map_mul]
    ext <;> simp <;> field_simp <;> ring
  · simp only [ha, hb, and_false, if_false, if_true, and_true] at hZab ⊢
    push_cast
    simp only [sub_zero, add_zero] at hZab ⊢
    rw [map_mul, map_mul, hZab]
    simp only [AlgEquiv.apply_symm_apply, he2, hα, map_mul]
    ext <;> simp <;> field_simp
  · simp only [ha, hb, false_and, if_false, if_true] at hZab ⊢
    push_cast
    simp only [sub_zero, add_zero, one_mul] at hZab ⊢
    rw [map_mul, hZab]
    simp only [AlgEquiv.apply_symm_apply, he1, hα, map_mul]
    ext <;> simp <;> field_simp
  · simp only [ha, hb, false_and, and_false, if_false] at hZab ⊢
    push_cast
    simp only [sub_zero, add_zero, one_mul, mul_one] at hZab ⊢
    rw [hZab]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
