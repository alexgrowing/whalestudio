import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.CoordGU

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

section StepsT

def AlgGUT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    IsUnit (Zh₁.submatrix Fin.castSucc Fin.castSucc).det → IsUnit (Zh₂.submatrix Fin.castSucc Fin.castSucc).det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

end StepsT

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem thetaMbeG_of_coordT (h1 : CoordGU) (h2 : AlgGUT) (M : Model F E) (r n : ℕ) : ThetaMbeG M r n := by
  intro hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂ hu₂
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hmode
  have hg := hyp.1
  have hr2 : IsUnit (H.Dl f₂ f₂' r) := by
    apply dl_unit_of_head hs H f₂ f₂' t₁.T t₁.T'
    have : headDet M Z₂ = ((HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T').submatrix Fin.castSucc
        Fin.castSucc).det := by
      unfold headDet; rw [e₂]
    rw [← this]; exact hu₂
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hunit : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    have : IsUnit (H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1)) := by rw [hrel]; exact hr2.mul (dl_succ_unit hyp)
    exact isUnit_of_mul_isUnit_right this
  have hzz : ∀ a b, HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b ∈ M.R := by
    intro a b
    have := (Z₂ a b).2
    rw [show ((Z₂ a b : M.R) : E) = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' a b from
      congrFun (congrFun e₂ a) b] at this
    exact this
  have hG1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
      (H.Dl t₁.f t₁.f' r * M.L.cj (H.Dl t₁.f t₁.f' r))) := by
    have hG : H.Gdet t₁.f t₁.f' t₁.T t₁.T' ≠ 0 := hg.1.2.2.2.2.1
    unfold HermSp.Gdet HermSp.normE at hG
    apply isUnit_of_cj_fixed g _ hG
    simp only [map_sub, map_mul, M.L.cj_cj, cj_alg]
    ring
  rw [h1 F E M g hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hunit hzz]
  refine h2 F E M g hs r t₁.T t₁.T' (hg.1.2.2.2.2.2 g hs).1 (hg.1.2.2.2.2.2 g hs).2.1 _ _ Z₁ Z₂ e₁ e₂
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hyp.1.1.2.1.2.2.2.1
  · rw [← dl_full]; exact dl_succ_unit hyp
  · rw [← dl_full]; exact hunit
  · rw [← dl_eq_det]; exact hD
  · rw [← dl_eq_det]; exact hr2
  · rw [← dl_full, ← dl_full, ← dl_eq_det, ← dl_eq_det]
    linear_combination hrel.symm
  · rw [← dl_full, ← dl_eq_det]
    exact hG1
  · rw [← dl_full, ← dl_eq_det]
    have key := gdet_rel (M := M) (H.Dl t₁.f t₁.f' (r + 1)) (H.Dl t₁.f t₁.f' r) (H.Dl f₂ f₂' (r + 1))
      (H.Dl f₂ f₂' r) (algebraMap F E (t₁.T * t₁.T')) hrel
    have hA : IsUnit (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) :=
      (dl_succ_unit hyp).mul ((dl_succ_unit hyp).map M.L.cj)
    have hB : IsUnit (H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1))) := hunit.mul (hunit.map M.L.cj)
    have : IsUnit ((H.Dl f₂ f₂' (r + 1) * M.L.cj (H.Dl f₂ f₂' (r + 1)) - algebraMap F E (t₁.T * t₁.T') *
        (H.Dl f₂ f₂' r * M.L.cj (H.Dl f₂ f₂' r))) * (H.Dl t₁.f t₁.f' (r + 1) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))) := by
      rw [key]; exact hB.mul hG1
    exact isUnit_of_mul_isUnit_left this

theorem locCntUG_of_algGUT (h : AlgGUT) : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG :=
  locCntUG_of (fun _ _ _ _ _ _ _ _ _ M _ r n => thetaMbeG_of_coordT coordGU_holds h M r n)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
