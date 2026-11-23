import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DuForm

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def uV (g : SplitG M.L) (l : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => ph1 g (l a)) (fun a => ph2 g (l a))

def qM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 1 0 (x • 1)

theorem pM_mul_qM (x : F) (hx : x ≠ 0) : pM r x⁻¹ * qM r x = 1 := by
  rw [pM, qM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> simp [smul_smul, mul_inv_cancel₀ hx]

theorem firstProj_iotaOne_cases (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g (iota1 hs l i : E) = match i with
      | Sum.inl a => ph1 g (l a)
      | Sum.inr a => (ph2 g (l a) - ph1 g (l a)) / (g.q : F) := by
  rcases i with a | a <;> simp [iota1, firstProj_apply, secondProj_apply]

theorem secondProj_iotaOne_eq_zero (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g (iota1 hs l i : E) = 0 := by
  rcases i with a | a <;> simp [iota1, secondProj_apply]

theorem vecMul_qM (hs : M.split = some g) (l : Fin (r + 1) → M.R) :
    Matrix.vecMul (fun i => ph1 g (iota1 hs l i : E)) (qM r (g.q : F)) = uV g l := by
  have hq := q_ne g
  funext k
  rcases k with a | a
  · simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, qM, firstProj_iotaOne_cases, uV, Matrix.one_apply]
  · simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, qM, firstProj_iotaOne_cases, uV, Matrix.one_apply]
    field_simp
    ring

theorem splitForm_iota_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    ph2 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) = 0 := by
  unfold formG
  simp [map_sum, map_mul, secondProj_iotaOne_eq_zero]

theorem splitForm_iota_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hG : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (l w : Fin (r + 1) → M.R) :
    ph1 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) =
      dotProduct (uV g l) (Matrix.mulVec (gHat g Zh T T')⁻¹ (uV g w)) := by
  set G := gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
  have hq := q_ne g
  have hcw : ∀ j, ph1 g ((M.L.cj : E →+* E) (iota2 hs w j : E)) = ph1 g (iota1 hs w j : E) := by
    intro j
    show ph1 g (M.L.cj (M.L.cj (iota1 hs w j : E))) = _
    rw [M.L.cj_cj]
  have h1 : ph1 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) =
      dotProduct (fun i => ph1 g (iota1 hs l i : E)) (Matrix.mulVec (G.map (ph1 g))⁻¹ fun j => ph1 g (iota1 hs w j : E)) := by
    rw [← map_inv_of (ph1 g) G hG]
    unfold formG
    simp only [map_sum, map_mul, hcw, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : (pM r (g.q : F)⁻¹)⁻¹ = qM r (g.q : F) := Matrix.inv_eq_right_inv (pM_mul_qM _ hq)
  have hPt : ((pM r (g.q : F)⁻¹).transpose)⁻¹ = (qM r (g.q : F)).transpose := by
    rw [← Matrix.transpose_nonsing_inv, hP]
  rw [h1, map_gramG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hP, hPt, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, vecMul_qM, vecMul_qM]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
