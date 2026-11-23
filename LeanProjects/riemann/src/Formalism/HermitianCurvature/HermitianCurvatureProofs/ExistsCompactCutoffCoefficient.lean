import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.PBI

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dmin_app (h : C.LPt) (hh : D.IsLocPt h r) (ζ : ℂ) {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r}
    (hZ : Zhat k r z z' γ = D.ptMatN (h ++ [(1, ζ)]) (r + 1)) :
    Dmin k r z z' γ ⟨r, by omega⟩ = (D.ptMatN h r).det := by
  unfold Dmin
  rw [hZ]
  have e := (Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app ζ h r hh.2).2
  rw [← e]
  congr 1

theorem vecV_congr_Dr (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (h : C.LPt)
    (hh : D.IsLocPt h r) (ζ : ℂ) {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ B.GPos Bs, Dmin k r Bs.z Bs.z' g ⟨r, by omega⟩ = (D.ptMatN h r).det → H₁ g = H₂ g) :
    D.vecV Bs ν' m₀ H₁ (h ++ [(1, ζ)]) = D.vecV Bs ν' m₀ H₂ (h ++ [(1, ζ)]) := by
  unfold D.vecV
  by_cases hq : D.IsLocPt (h ++ [(1, ζ)]) (r + 1) ∧
      0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r (h ++ [(1, ζ)])
  · simp only [dif_pos hq]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN (h ++ [(1, ζ)]) (r + 1) ∧
        D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := P.ptG_spec k r Bs.z Bs.z' _ h'.choose hq.1 h'.choose_spec.2.1
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ hq.2
      have hD := dmin_app h hh ζ h'.choose_spec.2.1
      have e := P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq.1.2 ▸ D.ptPerm (h ++ [(1, ζ)]))) H₁ H₂ 1 (by
        filter_upwards [P.B5.ae_inSS Bs] with p hp
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [hH _ ⟨P.B7.sgs_mem Bs hp hγ, by rw [P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
          (by rw [P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hD)])
      rw [e, one_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq]

end vec

section cut

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def cutD (Bs : B.RealPlaceData P.k P.r Wp Wq) (χ : ℂ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨P.r, by omega⟩) • F g

theorem cutD_ne {Bs : B.RealPlaceData P.k P.r Wp Wq} {χ : ℂ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {g : B.Mat P.k P.r} (h : cutD Bs χ F g ≠ 0) : F g ≠ 0 ∧ χ (Dmin P.k P.r Bs.z Bs.z' g ⟨P.r, by omega⟩) ≠ 0 := by
  refine ⟨fun h0 => h ?_, fun h0 => h ?_⟩
  · simp [cutD, h0]
  · simp [cutD, h0]

theorem cutD_cpt (Bs : B.RealPlaceData P.k P.r Wp Wq) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) : KB.CptCoef Bs (cutD Bs χ F) := by
  obtain ⟨hck, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  have hb : ContDiff ℝ ∞ (fun g : B.Mat P.k P.r => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨P.r, by omega⟩)) :=
    hχ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _)
  refine ⟨Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_rsmul hb hck, ⟨R, fun g hg hne => hR g hg (cutD_ne hne).1⟩, ε, hε,
    fun g hg hne => hεG g hg (cutD_ne hne).1⟩

theorem vector_eq_of_cutoff (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (hh : D.IsLocPt h P.r)
    (b : ContDiffBump (D.ptMatN h P.r).det) (w : List C.Letter) (hcut : KB.CutWord P p.l0 w)
    (e : Wd.Ix (Fin w.length)) (Cb : ℝ) (hdd : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (ζ : ℂ) :
    p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e (cutD p.T.base b F)) (h ++ [(1, ζ)]) := by
  unfold KB.Pl.V
  apply vecV_congr_Dr p.T.base p.ν' p.m₀ h hh ζ
  intro g hg hD
  obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hΘ⟩ := hdd w hcut e
  have hgdom : g ∈ C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
  rw [hΘ F g hgdom, hΘ _ g hgdom]
  have hcont : Continuous (fun x : B.Mat P.k P.r => Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨P.r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin p.T.base.z p.T.base.z' _).continuous
  have hOo : IsOpen {x : B.Mat P.k P.r | Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨P.r, by omega⟩ ∈
      Metric.ball (D.ptMatN h P.r).det b.rIn} := hcont.isOpen_preimage _ Metric.isOpen_ball
  refine Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop hOo (fun x hx => ?_) g ?_
  · simp only [cutD]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_smul]
  · show Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ ∈ Metric.ball (D.ptMatN h P.r).det b.rIn
    rw [hD]; exact Metric.mem_ball_self b.rIn_pos

end cut

section loc

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocOp (T : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  ∀ O : Set (B.Mat k r), IsOpen O → ∀ f₁ f₂ : B.Mat k r → E, (∀ x ∈ O, f₁ x = f₂ x) → ∀ x ∈ O, T f₁ x = T f₂ x

theorem locOp_eabH (a b : Fin (2 * r + k + 1)) : LocOp (k := k) (r := r) (E := E) (EabH (Hpk k r) a b) := by
  intro O hO f₁ f₂ h x hx
  simp only [EabH]
  rw [Formalism.FourierDecayAlt.P.JCTx6.Pos.rdV_congr_open hO h _ x hx, Formalism.FourierDecayAlt.P.JCTx6.Pos.rdV_congr_open hO h _ x hx]

theorem locOp_top (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (B.Mat k r → E) → (B.Mat k r → E))
    (hE : ∀ a b, LocOp (Eop a b)) (u : ℂ) (a b : Fin (2 * r + k + 1)) : LocOp (Formalism.QuantumDeterminants.Top Eop u a b) := by
  intro O hO f₁ f₂ h x hx
  simp only [Formalism.QuantumDeterminants.Top]
  rw [hE a b O hO f₁ f₂ h x hx, h x hx]

theorem locOp_foldr : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))), (∀ T ∈ L, LocOp T) →
    LocOp (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ _ _ h => h
  | T :: L, hL => by
    intro O hO f₁ f₂ h x hx
    simp only [List.foldr_cons]
    exact hL T List.mem_cons_self O hO _ _
      (locOp_foldr L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) O hO f₁ f₂ h) x hx

theorem locOp_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    LocOp (k := k) (r := r) (E := E) (qminorOp (EabH (Hpk k r)) a b u) := by
  intro O hO f₁ f₂ h x hx
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine locOp_foldr _ (fun T hT => ?_) O hO f₁ f₂ h x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact locOp_top _ (fun a b => locOp_eabH a b) _ _ _

theorem locOp_AAop (m : ℕ) (hm : m ≤ r) (u : ℂ) : LocOp (k := k) (r := r) (E := E) (C3.AAop k r m hm u) := by
  intro O hO f₁ f₂ h x hx
  simp only [C3.AAop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOp_qminorOp _ _ _ O hO f₁ f₂ h x hx]
  · rfl

theorem locOp_AAvop (m : ℕ) (hm : m ≤ r) (ell : ℂ) : LocOp (k := k) (r := r) (E := E) (C3.AAvop k r m hm ell) := by
  intro O hO f₁ f₂ h x hx
  simp only [C3.AAvop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOp_qminorOp _ _ _ O hO f₁ f₂ h x hx]
  · rfl

theorem locOp_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    LocOp (k := k) (r := r) (E := E) (D.vLet k r z z' j hj l e) := by
  intro O hO f₁ f₂ h x hx
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [locOp_AAop _ _ _ O hO f₁ f₂ h x hx]
  · rw [locOp_AAvop _ _ _ O hO f₁ f₂ h x hx]

theorem uwG_congr_open (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → E} (h : ∀ x ∈ O, f₁ x = f₂ x) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ x ∈ O, D.uwG k r z z' f₁ j hj w e x = D.uwG k r z z' f₂ j hj w e x
  | [], _ => h
  | l :: w, e => by
    intro x hx
    simp only [D.uwG]
    exact locOp_vLet z z' j hj l _ O hO _ _ (uwG_congr_open z z' j hj hO h w _) x hx

end loc

section slice

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) (j : ℕ)
    (hj : j < b + 2) (hj' : j < a + 2) :
    Dmin k b z z' (D.castM e g) ⟨j, hj⟩ = Dmin k a (D.castV e.symm z) (D.castV e.symm z') g ⟨j, hj'⟩ := by
  subst e
  rw [JCTx5.castM_rfl, JCTx5.castV_rfl, JCTx5.castV_rfl]

theorem dmin_gaXi {p ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
    (γ : B.Mat k ρ) (z z' : Fin (2 * (p + 0 + ρ) + k + 1) → ℂ) :
    Dmin k (p + 0 + ρ) z z' (U.gaXi k ρ σ d ξ Z γ) ⟨p + 0, by omega⟩ = (U.hMat σ d).det := by
  rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k (p + 0) ρ z z' _,
    Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice σ d ξ Z γ]
  simp [G.detM]

theorem sliceAt_congr_Dr {r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (h : C.LPt) (hp : D.ptSize h ≤ r)
    {G₁ G₂ : B.Mat k r → E}
    (hG : ∀ x, Dmin k r z z' x ⟨D.ptSize h, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det → G₁ x = G₂ x) :
    D.sliceAt k r z z' G₁ h = D.sliceAt k r z z' G₂ h := by
  unfold D.sliceAt
  rw [dif_pos hp, dif_pos hp]
  funext γ
  unfold U.PhiFun
  congr 1
  funext ξ
  congr 1
  simp only [D.castF]
  apply hG
  rw [dmin_castM (by omega) z z' _ _ _ (by omega)]
  exact dmin_gaXi _ _ ξ _ γ _ _

theorem det_hMat_pt (h : C.LPt) :
    (U.hMat (D.ptPerm h) (D.ptDiag h)).det = (D.ptMatN h (D.ptSize h)).det := by
  rw [← Formalism.FourierDecayAlt.P.Dx1.monomialMatrix_eq_hMat _ _ (Formalism.FourierDecayAlt.P.Dx1.ptPerm_invol h), ← Formalism.FourierDecayAlt.P.Dx1.ptMat_monoP]
  rfl

end slice

section cutslice

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_eq_of_cutoff (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (hh : D.IsLocPt h P.r)
    (b : ContDiffBump (D.ptMatN h P.r).det) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) :
    KB.slv p.T F P.r le_rfl w h hh.2 e = KB.slv p.T (cutD p.T.base b F) P.r le_rfl w h hh.2 e := by
  unfold KB.slv
  congr 1
  apply sliceAt_congr_Dr _ _ h (by rw [hh.2])
  intro x hx
  have hcont : Continuous (fun x : B.Mat P.k P.r => Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨P.r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin p.T.base.z p.T.base.z' _).continuous
  have hOo : IsOpen {x : B.Mat P.k P.r | Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨P.r, by omega⟩ ∈
      Metric.ball (D.ptMatN h P.r).det b.rIn} := hcont.isOpen_preimage _ Metric.isOpen_ball
  refine uwG_congr_open _ _ _ _ hOo (fun y hy => ?_) w e x ?_
  · simp only [cutD]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]
  · show Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨P.r, by omega⟩ ∈ Metric.ball (D.ptMatN h P.r).det b.rIn
    have e1 : (⟨P.r, by omega⟩ : Fin (P.r + 2)) = ⟨D.ptSize h, by rw [hh.2]; omega⟩ := Fin.ext hh.2.symm
    rw [e1, hx, det_hMat_pt, hh.2]
    exact Metric.mem_ball_self b.rIn_pos

end cutslice

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBI

theorem exists_compact_cutoff_coefficient {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef p.T.base F) (h : C.LPt) (hh : D.IsLocPt h P.r) :
    ∃ F₁ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₁ ∧
      (∀ w, KB.CutWord P p.l0 w → ∀ (e : Wd.Ix (Fin w.length)) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
        ∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e F₁) (h ++ [(1, ζ)])) ∧
      (∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
        KB.slv p.T F P.r le_rfl w h hh.2 e = KB.slv p.T F₁ P.r le_rfl w h hh.2 e) ∧
      ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧
        ∀ g, F₁ g ≠ 0 → Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ ∈ K := by
  set c0 := (D.ptMatN h P.r).det with hc0
  have hc0ne : c0 ≠ 0 := det_ptMatN_ne h P.r hh
  have hn : 0 < ‖c0‖ := norm_pos_iff.mpr hc0ne
  let b : ContDiffBump c0 := ⟨‖c0‖ / 4, ‖c0‖ / 2, by positivity, by linarith⟩
  refine ⟨cutD p.T.base b F, cutD_cpt p.T.base b.contDiff hF,
    fun w hcut e Cb hdd ζ => vector_eq_of_cutoff p F h hh b w hcut e Cb hdd ζ,
    fun w e => slice_eq_of_cutoff p F h hh b w e, Metric.closedBall c0 (‖c0‖ / 2), isCompact_closedBall _ _, ?_, ?_⟩
  · intro h0
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at h0
    linarith
  · intro g hg
    have h2 := (cutD_ne hg).2
    have hs : Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ ∈ Function.support b := h2
    rw [b.support_eq] at hs
    exact Metric.ball_subset_closedBall hs

end Formalism.FourierDecayAlt.P
