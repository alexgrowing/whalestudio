import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LeadingMinorSecondProj

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem mem_headCols_iff (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (l : Fin (r + 1) → M.R) :
    l ∈ headCols Z ↔ ∃ w : Fin (r + 1) → M.R, w (Fin.last r) = 0 ∧ Z.mulVec w = l := by
  constructor
  · intro hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨Pi.single a.castSucc 1, by simp [(Fin.castSucc_lt_last a).ne], ?_⟩
      rw [← col_eq_mulVec]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', by simp [hw, hw'], Matrix.mulVec_add _ _ _⟩
    | smul s x _ hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨s • w, by simp [hw], Matrix.mulVec_smul _ _ _⟩
  · rintro ⟨w, hw, rfl⟩
    exact mulVec_mem_headCols _ _ hw

theorem llMap_of_last (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (w : Fin (r + 1) → M.R)
    (hw : w (Fin.last r) = 0) : llMap hs Z TT w = Z.Z.mulVec w := by
  show Z.Z.mulVec w - (TT * dgR hs (trO hs (w (Fin.last r)))) • eV r = _
  rw [hw, map_zero, map_zero, mul_zero, zero_smul, sub_zero]

theorem headCols_le_LL (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) {l : Fin (r + 1) → M.R}
    (hl : l ∈ headCols Z.Z) : l ∈ LL hs Z TT := by
  obtain ⟨w, hw, rfl⟩ := (mem_headCols_iff Z.Z l).1 hl
  exact ⟨w, llMap_of_last hs Z TT w hw⟩

theorem firstQuotient_eq_zero_iff (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (l : Fin (r + 1) → M.R) :
    mk1 hs Z TT l = 0 ↔ ∃ m, llMap hs Z TT m = l := by
  rw [mk1, QuotientAddGroup.eq_zero_iff]
  rfl

theorem ker_fact (hs : M.split = some g) (T T' : F) (TT : M.R) (hTT : g.e (TT : E) = (T, T'))
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det)
    (hG : IsUnit (Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)))
    (l : Fin (r + 1) → M.R) (h1 : mk1 hs Z TT l = 0) (h2 : laG (ZZm g Zh T T') l = 0) :
    l ∈ headCols Z.Z := by
  obtain ⟨m, rfl⟩ := (firstQuotient_eq_zero_iff hs Z TT l).1 h1
  rw [laG_llMap hs Zh T T' Z hZ hu] at h2
  have hq := q_ne g
  have hd1 := ((isUnit_iff_ph (g := g) _).1 hu).1
  have hd2 := ((isUnit_iff_ph (g := g) _).1 hu).2
  have hG1 := ((isUnit_iff_ph (g := g) _).1 hG).1
  have ecj : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    rw [firstProj_apply, secondProj_apply, g.e_cj]; rfl
  have eal1 : ∀ c : F, ph1 g (algebraMap F E c) = c := fun c => by rw [firstProj_apply, AlgEquiv.commutes]; rfl
  have eal2 : ∀ c : F, ph2 g (algebraMap F E c) = c := fun c => by rw [secondProj_apply, AlgEquiv.commutes]; rfl
  have et1 : ph1 g (tau0 g T T') = -T / (g.q : F) := by simp [firstProj_apply]
  have et2 : ph2 g (tau0 g T T') = T' / (g.q : F) := by simp [secondProj_apply]
  have eT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have eT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  set a := ph1 g ((m (Fin.last r) : M.R) : E) with ha
  set b := ph2 g ((m (Fin.last r) : M.R) : E) with hb
  have etr : ((trO hs (m (Fin.last r)) : 𝒪[F]) : F) = (a - b) / (g.q : F) := by rw [trO_coe]; rfl
  have H1 := congrArg (ph1 g) h2
  have H2 := congrArg (ph2 g) h2
  simp only [map_sub, map_mul, map_one, map_zero, eal1, eal2, et1, et2, eT1, eT2, etr,
    cornerRatio_firstProj hs Zh T T' hu, cornerRatio_secondProj hs Zh T T' hu] at H1 H2
  rw [← ha] at H1
  rw [← hb] at H2
  have E1 : a * ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * b = 0 := by
    field_simp [hd1, hq] at H1
    linear_combination H1
  have E2 : b * ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * a = 0 := by
    field_simp [hd2, hq] at H2
    linear_combination H2
  have hG1' : ph1 g Zh.det * ph2 g Zh.det - T * T' * (ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det *
      ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0 := by
    simpa [map_sub, map_mul, ecj, eal1] using hG1
  have ha0 : a = 0 := by
    have : a * (ph1 g Zh.det * ph2 g Zh.det - T * T' * (ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det *
        ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det)) = 0 := by
      linear_combination ph2 g Zh.det * E1 - T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det * E2
    exact (mul_eq_zero.1 this).resolve_right hG1'
  have hb0 : b = 0 := by
    rw [ha0, mul_zero, add_zero] at E2
    exact (mul_eq_zero.1 E2).resolve_right hd2
  have hm : m (Fin.last r) = 0 := by
    apply Subtype.ext
    apply g.e.injective
    rw [ZeroMemClass.coe_zero, map_zero]
    exact Prod.ext ha0 hb0
  rw [llMap_of_last hs Z TT m hm]
  exact mulVec_mem_headCols _ _ hm

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
