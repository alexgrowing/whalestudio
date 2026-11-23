import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength

namespace Formalism.MainNotions

theorem JointEigenvalueBoundsFromAnyDatum.first_hypothesis_of_lifting (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm1 D :=
  fun F _ _ _ E _ _ _ _ M hM => h.2.1 F E M hM

theorem JointEigenvalueBoundsFromAnyDatum.second_hypothesis_of_lifting (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm2 D :=
  fun F _ _ _ E _ _ _ _ M hM => h.2.2 F E M hM

theorem JointEigenvalueBoundsFromAnyDatum.integrality_of_commutation (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm3 D :=
  fun hk => (h.1 hk).1

theorem JointEigenvalueBoundsFromAnyDatum.fourth_hypothesis_of_lifting (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.ArchimedeanSignatureMatching D C :=
  fun hk => (h.1 hk).2.1

theorem JointEigenvalueBoundsFromAnyDatum.sizes_bound_of_log_estimates (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm5 D :=
  fun hk => (h.1 hk).2.2.1

theorem JointEigenvalueBoundsFromAnyDatum.lifting_bounds_of_theorem_c (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm10 D :=
  fun hk => (h.1 hk).2.2.2

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem JointEvBounds.ownEv_of_all {P : ∀ x, Fm.Ix x → Prop} (h : ∀ x i, P x i) :
    S.OwnEv Fm fun _ _ x i => P x i :=
  ⟨0, fun x _ i => h x i⟩

theorem JointEigenvalueBoundsFromAnyDatum.theta_norm_family_of_linked (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF1 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.first_hypothesis_of_lifting _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.theta_condition_family_of_linked (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF2 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.second_hypothesis_of_lifting _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.stabiliser_family_of_definite (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF3 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.integrality_of_commutation _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.injectivity_family_of_theorem (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF4 Fm :=
  let ⟨C, h⟩ := h; ⟨C, JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.fourth_hypothesis_of_lifting _ C (h x i)⟩

theorem JointEigenvalueBoundsFromAnyDatum.family_ev_bound_of_source (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF5 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.sizes_bound_of_log_estimates _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.familyRowsCount_of_thinScalesBound (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.FamilyRowsCountHypothesis Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.lifting_bounds_of_theorem_c _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.AdmF_of {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, S.TermTie (Fm.D x i)}
    (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), S.LocalSplitGroups.TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
    (h : ThinScalesBound.OrbitValuationBound Fm) (h6 : JointEigenvalueBoundsFromAnyDatum.admF6 Fm) (h7 : JointEigenvalueBoundsFromAnyDatum.admF7 Fm) (h8 : JointEigenvalueBoundsFromAnyDatum.admF8 Fm X cN)
    (h9 : JointEigenvalueBoundsFromAnyDatum.admF9 Fm X) : JointEigenvalueBoundsFromAnyDatum.AdmF Fm X cN :=
  ⟨JointEigenvalueBoundsFromAnyDatum.theta_norm_family_of_linked Fm h, JointEigenvalueBoundsFromAnyDatum.theta_condition_family_of_linked Fm h, JointEigenvalueBoundsFromAnyDatum.stabiliser_family_of_definite Fm h, JointEigenvalueBoundsFromAnyDatum.injectivity_family_of_theorem Fm h,
    JointEigenvalueBoundsFromAnyDatum.family_ev_bound_of_source Fm h, h6, h7, h8, h9, JointEigenvalueBoundsFromAnyDatum.familyRowsCount_of_thinScalesBound Fm h⟩

end Family

end Formalism.MainNotions
