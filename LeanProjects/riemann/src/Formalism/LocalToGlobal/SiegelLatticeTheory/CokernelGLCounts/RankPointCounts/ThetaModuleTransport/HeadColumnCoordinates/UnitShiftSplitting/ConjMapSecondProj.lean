import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AdeleInfiniteComponentApply

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

def dl (r : ℕ) (b : Fin (r + 1)) : F := if b = Fin.last r then 1 else 0

theorem e_ueq (η : M.R) (l : Fin (r + 1) → M.R) (b : Fin (r + 1)) :
    g.e ((((η • (eV r : Fin (r + 1) → M.R) + q2 hs • l) : Fin (r + 1) → M.R) b : M.R) : E) =
      (p1 g η * dl r b, p2 g η * dl r b + (g.q : F) * p2 g (l b)) := by
  have he : g.e (((eV r : Fin (r + 1) → M.R) b : M.R) : E) = ((dl r b : F), (dl r b : F)) := by
    by_cases hb : b = Fin.last r
    · subst hb
      rw [show (((eV r : Fin (r + 1) → M.R) (Fin.last r) : M.R) : E) = 1 by simp [eV], map_one]
      simp only [dl, if_true]
      rfl
    · rw [show (((eV r : Fin (r + 1) → M.R) b : M.R) : E) = 0 by simp [eV, hb], map_zero]
      simp only [dl, if_neg hb]
      rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, AddMemClass.coe_add, MulMemClass.coe_mul, map_add,
    map_mul, he, embedding_uniformizer]
  ext
  · simp [p1]
  · simp [p2]

theorem conj_map_firstProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map (p1 g) = Zh.map (p2 g) := by
  ext i j
  simp [p1, p2, g.e_cj]

theorem conj_map_secondProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (Zh.map M.L.cj).map (p2 g) = Zh.map (p1 g) := by
  ext i j
  simp [p1, p2, g.e_cj]

theorem sum_dl (x : Fin (r + 1) → F) : ∑ b, x b * dl r b = x (Fin.last r) := by
  simp [dl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

end Formalism.L2.SG.LocalCountModules.AlgGSplit
