import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AlgGUNS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzplusDetUnit

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

def ScaleChoiceP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F),
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    T ∈ 𝒪[F] →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    ∃ α : E, α * M.L.cj α = 1 ∧ α ∈ M.L.O ∧ (α - 1) * algebraMap F E ((g.q : F)⁻¹) ∈ M.L.O ∧
      ∃ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
        Z₁'.map M.R.subtype = HermSp.ZZplusOf M (Zh₁ * dlast r α) T T' ∧
        Z₂'.map M.R.subtype = HermSp.ZZplusOf M (Zh₂ * dlast r α) T T' ∧
        IsUnit (Z₁'.map M.R.subtype).det ∧ IsUnit (Z₂'.map M.R.subtype).det ∧
        IsUnit (HermSp.ZZplusOf M ((Zh₁ * dlast r α).map M.L.cj) T T').det ∧
        IsUnit (HermSp.ZZplusOf M ((Zh₂ * dlast r α).map M.L.cj) T T').det ∧
        Nat.card (IsoMbe Z₁' Z₂') = Nat.card (IsoMbe Z₁ Z₂)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

theorem zz_split (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    HermSp.ZZplusOf M Zh T T' = ZZm g Zh T T' +
      Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F))) := by
  unfold ZZm
  ext a b
  simp only [Matrix.add_apply, Matrix.of_apply, cor]
  split_ifs
  · have h0 : g.e.symm (-T / (g.q : F), T' / (g.q : F)) + g.e.symm (T / (g.q : F), -T' / (g.q : F)) = 0 := by
      rw [← map_add, Prod.mk_add_mk]
      have e : (-T / (g.q : F) + T / (g.q : F), T' / (g.q : F) + -T' / (g.q : F)) = (0 : F × F) :=
        Prod.ext (by simp [neg_div]) (by simp [neg_div])
      rw [e, map_zero]
    rw [add_assoc, h0, add_zero]
  · simp

include hs in

theorem zz_unit_iff (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    IsUnit (HermSp.ZZplusOf M Zh T T').det ↔
      ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 ∧
        ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
  have hq : ((g.q : F)) ≠ 0 := fun h => g.q_irr.ne_zero (by ext; simpa using h)
  have hcor1 : (Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F)))).map (ph1 g) = Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM r (T / (g.q : F)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, cor, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM]
    split_ifs <;> simp [firstProj_apply]
  have hcor2 : (Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F)))).map (ph2 g) = Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM r (-T' / (g.q : F)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, cor, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM]
    split_ifs <;> simp [secondProj_apply]
  have hd1 : (Zh.map (ph1 g)).det = ph1 g Zh.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hd2 : (Zh.map (ph2 g)).det = ph2 g Zh.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hs1 : ((Zh.map (ph1 g)).submatrix Fin.castSucc Fin.castSucc).det =
      ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]
  have hs2 : ((Zh.map (ph2 g)).submatrix Fin.castSucc Fin.castSucc).det =
      ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]
  have e1 : ph1 g (HermSp.ZZplusOf M Zh T T').det = ((g.q : F)⁻¹) ^ (r + 1) *
      (ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, zz_split, Matrix.map_add _ (map_add _), zzMinus_firstProj_smul hs, hcor1,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.det_add_cornerM]
    have es : ∀ (c : F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F),
        ((c • A).submatrix Fin.castSucc Fin.castSucc).det = c ^ r * (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro c A
      have : (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc := by
        ext i j
        rfl
      rw [this, Matrix.det_smul, Fintype.card_fin]
    rw [Matrix.det_smul, Fintype.card_fin, es, hd1, hs1]
    ring
  have e2 : ph2 g (HermSp.ZZplusOf M Zh T T').det = (-((g.q : F)⁻¹)) ^ (r + 1) *
      (ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, zz_split, Matrix.map_add _ (map_add _), zzMinus_secondProj_transpose hs, hcor2,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.det_add_cornerM]
    have es : ∀ (c : F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F),
        ((c • A).submatrix Fin.castSucc Fin.castSucc).det = c ^ r * (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro c A
      have : (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc := by
        ext i j
        rfl
      rw [this, Matrix.det_smul, Fintype.card_fin]
    have et : ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) F,
        (A.transpose.submatrix Fin.castSucc Fin.castSucc).det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro A
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    rw [Matrix.det_smul, Fintype.card_fin, es, Matrix.det_transpose, et, hd2, hs2]
    ring
  rw [isUnit_iff_ph (g := g), e1, e2, mul_ne_zero_iff, mul_ne_zero_iff]
  simp only [ne_eq, pow_eq_zero_iff', inv_eq_zero, neg_eq_zero, hq, false_and, not_false_eq_true, true_and]

theorem dlast_det {K : Type} [CommRing K] (δ : K) : (dlast r δ).det = δ := by
  unfold dlast
  rw [Matrix.det_diagonal, Finset.prod_ite_eq']
  simp

theorem head_mul_dlast {K : Type} [CommRing K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (δ : K) :
    (A * dlast r δ).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
