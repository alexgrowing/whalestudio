import Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCutInside
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def hsLE {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp') :
    (Wq' →L[ℂ] Wp') →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq') => Wp') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => B.hsVec (Eρ.comp X)
      map_add' := fun X Y => by rw [ContinuousLinearMap.comp_add]; unfold B.hsVec; rfl
      map_smul' := fun c X => by rw [ContinuousLinearMap.comp_smul]; exact PBL.hsVec_smul c _ }

theorem hsLE_apply {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp')
    (X : Wq' →L[ℂ] Wp') : hsLE Eρ X = B.hsVec (Eρ.comp X) := rfl

theorem vecV_nonloc {P : M.Par} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData P.k P.r Wp' Wq')
    (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (Q : C.LPt)
    (hQ : ¬ D.IsLocPt Q (P.r + 1)) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dif_neg (fun h => hQ h.1)]

theorem gN_top_gram {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (a : List C.Letter)
    (ha : D.AdmAt S v a) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : I → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] PBL.HV S v),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef (p v).T.base (Fi i)) ∧
      ∀ P Q : C.LPt, KB.gN (PBL.setC S p F) v ε (S.G.r + 1) a P Q =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length Q : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S Q)),
          (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P))⟫_ℂ := by
  classical
  have hgpos := PBL.g_pos_of_built hB
  have hTT := (PBL.pdG_of_built hB v).2
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGr, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hcutw : KB.CutWord (D.parOf S v) (p v).l0 a := by
    obtain ⟨w, hw⟩ := ha
    rw [hl0, ← hw]
    exact PBD.cutWord_of_adm S hGr (PBCut.cutInside_of_built hB) w v
  have hInD' : KB.InDDplus2 (D.parOf S v) (p v).l0 (p v).T.base Cb (p v).Θ := by rw [hl0]; exact hInD
  have hTh : ∀ e : Wd.Ix (Fin a.length), ∃ F' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      KB.CptCoef (p v).T.base F' ∧ ∀ Q, (p v).V ((p v).Θ.Θ a e (F v ε)) Q = (p v).V F' Q := by
    intro e
    obtain ⟨F', hF', -, hV⟩ := Formalism.FourierDecayAlt.P.theta_compact_support _ _ (D.parOf S v) (p v) (F v ε) a e Cb hInD'
      (hF v ε hε) hcutw
    exact ⟨F', hF', hV⟩
  choose Fe hFe hVe using hTh
  have hΓ : PBL.ΓS S (S.G.r + 1) = 1 := by simp [PBL.ΓS, D.GamLev]
  refine ⟨Wd.Ix (Fin a.length) × M.Ty (D.parOf S v), inferInstance,
    fun i => PBL.del2 S p v a i.1 i.2 / (PBL.ΓS S (S.G.r + 1) * S.sizeAt v a), fun i => Fe i.1,
    fun i => hsLE ((p v).TP.E i.2), fun i => ?_, fun i => hFe i.1, fun P Q => ?_⟩
  · rw [hΓ, one_mul]
    exact div_nonneg (PBL.second_defect_nonneg S p v a i.1 i.2) (PBL.sizeAt_nonneg S v a)
  by_cases hloc : D.IsLocPt P (S.G.r + 1) ∧ D.IsLocPt Q (S.G.r + 1)
  · obtain ⟨hPl, hQl⟩ := hloc
    have hPs : D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hPl
    have hQs : D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hQl
    rw [PBL.gN_setC hB, PBL.rr_top_eq Formalism.FourierDecayAlt.P.vector_valued_types (p v) (F v ε) a _ _ hPs hQs]
    unfold Top.topOf
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    dsimp only
    have e1 := hVe e (PBL.stdS S P)
    have e2 := hVe e (PBL.stdS S Q)
    unfold KB.Pl.V at e1 e2
    rw [e1, e2, inner_smul_left, inner_smul_right, hsLE_apply, hsLE_apply]
    have hin : ⟪B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S Q))),
        B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S P)))⟫_ℂ =
        B.hsInner (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S P)))
          (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S Q))) := rfl
    rw [hin]
    set TT := Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z' with hTTdef
    by_cases h1 : 0 < D.ptG TT S.G.r (PBL.stdS S P)
    · by_cases h2 : 0 < D.ptG TT S.G.r (PBL.stdS S Q)
      · have hw1 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h1.le) _
        have hw2 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h2.le) _
        have hd1 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S P) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw1 _
        have hd2 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S Q) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw2 _
        rw [hd1, hd2]
        unfold omN PBL.del2
        rw [← hTT]
        simp only [Complex.conj_ofReal]
        push_cast
        ring
      · rw [PBL.vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, PBL.hsInner_zero_right']
        simp
    · rw [PBL.vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, PBD.hsInner_zero_left]
      simp
  · rw [PBL.gN_setC_zero hB F v ε (S.G.r + 1) a P Q hloc]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hPl : D.IsLocPt P (S.G.r + 1)
    · have hQl : ¬ D.IsLocPt Q (S.G.r + 1) := fun h => hloc ⟨hPl, h⟩
      have hQs : ¬ D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := fun h =>
        hQl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S Q) hQs, map_zero, smul_zero,
        inner_zero_left, mul_zero]
    · have hPs : ¬ D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := fun h =>
        hPl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S P) hPs, map_zero, smul_zero,
        inner_zero_right, mul_zero]

end

end Formalism.FourierDecayAlt.P.GermRateSplit
