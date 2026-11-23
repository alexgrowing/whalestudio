import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScalingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOfZeroDimVarietyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantWeightGapShiftStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.RefTower

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsOver_map {F E : Type} [Field F] [Field E] (f : F →+* E) {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → F} (hz : z ∈ ptsOver F P) : (fun p => f (z p)) ∈ ptsOver E P := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun k => ?_, fun p hp => ?_⟩
  · obtain ⟨i, hi⟩ := h1 k
    exact ⟨i, (map_ne_zero f).mpr hi⟩
  · have e := congrArg f (h2 p hp)
    rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left] at e
    rw [MvPolynomial.aeval_def]
    rwa [show f.comp (algebraMap _ F) = algebraMap _ E from Subsingleton.elim _ _] at e

theorem ptsOver_of_map {F E : Type} [Field F] [Field E] (f : F →+* E) {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → F} (hz : (fun p => f (z p)) ∈ ptsOver E P) : z ∈ ptsOver F P := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun k => ?_, fun p hp => ?_⟩
  · obtain ⟨i, hi⟩ := h1 k
    exact ⟨i, (map_ne_zero f).mp hi⟩
  · have e := h2 p hp
    rw [MvPolynomial.aeval_def, ← show f.comp (algebraMap _ F) = algebraMap _ E from Subsingleton.elim _ _] at e
    have e2 : f (MvPolynomial.eval₂ (algebraMap _ F) z p) = 0 := by
      rw [MvPolynomial.eval₂_comp_left]
      exact e
    rw [MvPolynomial.aeval_def]
    exact f.injective (e2.trans (map_zero f).symm)

end Points

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem ptsOver_mono {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type} [Field F]
    {P W : Ideal (MRing ι)} (h : P ≤ W) {z : (Σ k, ι k) → F} (hz : z ∈ ptsOver F W) : z ∈ ptsOver F P :=
  ⟨hz.1, fun g hg => hz.2 g (h hg)⟩

theorem rootHt_affine (R : RootModel Ψ N) (mu : Wt Ψ N) (s : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) : rootHt R 1 mu s L w = rootHt R 1 mu 0 L w + s * rootHt R 1 0 1 L w := by
  unfold rootHt
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases j with _ | r <;> simp [RootModel.coef] <;> ring

theorem line_smooth (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem l1_le_card_mul_norm (mu : Wt Ψ N) : l1 mu ≤ (Fintype.card Ψ * N : ℝ) * ‖mu‖ := by
  unfold l1
  calc ∑ τ, ∑ i, |mu τ i| ≤ ∑ τ : Ψ, ∑ i : Fin N, ‖mu‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => by
          rw [← Real.norm_eq_abs]
          exact (norm_le_pi_norm (mu τ) i).trans (norm_le_pi_norm mu τ)
    _ = (Fintype.card Ψ * N : ℝ) * ‖mu‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem collect {C C₁ G s b l x y H a : ℝ} (hC₁ : 1 ≤ C₁) (hG : 0 ≤ G) (hs : 0 < s) (hs1 : s ≤ 1) (hb : 0 ≤ b)
    (hl : 0 ≤ l) (hx : -C₁ ≤ x) (ha : 0 ≤ a) (hal : a ≤ G)
    (hy : -(C₁ * Real.log (2 + C₁ + x)) - C₁ ≤ y)
    (hH : (-(C * l) - C) - (a + |s|) * (C * b) ≤ H - (y + s * x)) :
    s * x - (C₁ + |C| * (G + 2) + 1) * Real.log (2 + (C₁ + |C| * (G + 2) + 1) + x) -
      (C₁ + |C| * (G + 2) + 1) * l - (C₁ + |C| * (G + 2) + 1) * b - (C₁ + |C| * (G + 2) + 1) ≤ H := by
  have hsabs : |s| = s := abs_of_pos hs
  have hCabs : C ≤ |C| := le_abs_self C
  have hCnn : 0 ≤ |C| := abs_nonneg C
  obtain ⟨D, hD⟩ : ∃ D, D = C₁ + |C| * (G + 2) + 1 := ⟨_, rfl⟩
  rw [← hD]
  have hG2 : |C| ≤ |C| * (G + 2) := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ G + 2) hCnn]
  have hCD : C₁ ≤ D := by rw [hD]; nlinarith
  have hCD' : |C| ≤ D := by rw [hD]; nlinarith
  have hC1C : C₁ + C ≤ D := by rw [hD]; nlinarith
  have hx2 : 0 < 2 + C₁ + x := by linarith
  have hlog1 : 0 ≤ Real.log (2 + C₁ + x) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 + C₁ + x) ≤ Real.log (2 + D + x) := Real.log_le_log hx2 (by linarith)
  have hlogterm : C₁ * Real.log (2 + C₁ + x) ≤ D * Real.log (2 + D + x) :=
    mul_le_mul hCD hlog2 hlog1 (by linarith)
  have h1 : C * l ≤ D * l := mul_le_mul_of_nonneg_right (by linarith) hl
  have haC : (a + s) * C ≤ D := by
    have e1 : (a + s) * C ≤ (a + s) * |C| := mul_le_mul_of_nonneg_left hCabs (by linarith)
    have e2 : (a + s) * |C| ≤ (G + 1) * |C| := mul_le_mul_of_nonneg_right (by linarith) hCnn
    have e3 : (G + 1) * |C| ≤ D := by rw [hD]; nlinarith
    linarith
  have h2 : (a + |s|) * (C * b) ≤ D * b := by
    rw [hsabs, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right haC hb
  linarith

theorem transfer [DecidableEq Ψ] (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω)
    (c t s lo hi : ℝ) (lam : Wt Ψ N) (hC : Close M R i u c) (hA : ArchBetween M R i u t lam s lo hi)
    (L : Type) [Field L] [NumberField L] (w : (Σ k, M.ι k) → L) (hw : w ∈ ptsOver L M.P) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (v : (Σ k, R.ι k) → F), v ∈ ptsOver F R.P ∧
      rootHt M t lam s L w - rootHt R 1 lam s F v ∈
        Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  classical
  have hw' : (fun p => algebraMap L (AlgebraicClosure L) (w p)) ∈ ptsOver (AlgebraicClosure L) M.P :=
    ptsOver_map (algebraMap L (AlgebraicClosure L)) hw
  obtain ⟨-, -, hpts, hlift⟩ := GlobalTheory.T.join_model_points_project Ψ N M R i
  obtain ⟨z, hz, hzw⟩ := hlift (AlgebraicClosure L) _ hw'
  let F := IntermediateField.adjoin L (Set.range z)
  haveI : FiniteDimensional L F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans L F }
  let z' : _ → F := fun p => ⟨z p, IntermediateField.subset_adjoin L _ ⟨p, rfl⟩⟩
  have hz' : z' ∈ ptsOver F (mCoordIdeal (joinOf M R i)) :=
    ptsOver_of_map (algebraMap F (AlgebraicClosure L)) hz
  refine ⟨F, inferInstance, inferInstance, fun p => z' (GlobalTheory.CompanionTheory.Ar.Cmp.joinInr M.ι R.ι p), (hpts F z' hz').2, ?_⟩
  have key := GlobalTheory.T.root_height_difference_bound Ψ N M R i u c t s lo hi lam hC hA F z' hz'
  have heq : rootHt M t lam s F (fun p => z' (GlobalTheory.CompanionTheory.Ar.Cmp.joinInl M.ι R.ι p)) = rootHt M t lam s L w := by
    unfold rootHt
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← GlobalTheory.T.line_height_invariant_scaling M.K M.ι (M.line t j) L F (algebraMap L F) w (fun _ => 1) hw.1 (fun _ => one_ne_zero)]
    congr 1
    funext p
    rw [one_mul]
    apply Subtype.ext
    show z (GlobalTheory.CompanionTheory.Ar.Cmp.joinInl M.ι R.ι p) = _
    rw [congrFun hzw p]
    rfl
  rw [heq] at key
  exact key

theorem point_bound [DecidableEq Ψ] {II : IntersectionSystem} (hII : IsIntersectionSystem II) (M R : RootModel Ψ N)
    (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) {C C₁ G t s b l : ℝ} (mu : Wt Ψ N)
    (hC₁ : 1 ≤ C₁) (hG : 0 ≤ G) (hs : 0 < s) (hs1 : s ≤ 1) (hb : 0 ≤ b) (hl : 0 ≤ l) (hmu : l1 mu ≤ G)
    (hRef : ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P, -C₁ ≤ rootHt R 1 0 1 L w ∧
      -(C₁ * Real.log (2 + C₁ + rootHt R 1 0 1 L w)) - C₁ ≤ rootHt R 1 mu 0 L w)
    (hClose : Close M R i u (C * b)) (hA : ArchBetween M R i u t mu s (-(C * l) - C) C)
    {W : Ideal (MRing M.ι)} (hW : M.IsPt W) :
    ∃ x, -C₁ ≤ x ∧ s * x - (C₁ + |C| * (G + 2) + 1) * Real.log (2 + (C₁ + |C| * (G + 2) + 1) + x) -
      (C₁ + |C| * (G + 2) + 1) * l - (C₁ + |C| * (G + 2) + 1) * b - (C₁ + |C| * (G + 2) + 1) ≤
        M.ht II t mu s W := by
  obtain ⟨L, _, _, w, hWw, hwW, hII'⟩ := GlobalTheory.T.height_of_zero_dim_variety M.K M.ι II hII W hW.1
  have hwP : w ∈ ptsOver L M.P := ptsOver_mono hW.2 hwW
  have hht : M.ht II t mu s W = rootHt M t mu s L w := by
    unfold RootModel.ht rootHt
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_div_assoc, hII' _ (line_smooth M t j)]
  obtain ⟨F, _, _, v, hv, hIcc⟩ := transfer M R i u (C * b) t s (-(C * l) - C) C mu hClose hA L w hwP
  obtain ⟨hx, hy⟩ := hRef F v hv
  refine ⟨rootHt R 1 0 1 F v, hx, ?_⟩
  rw [hht]
  have hl1 : 0 ≤ l1 mu := Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  refine collect (a := l1 mu) (y := rootHt R 1 mu 0 F v) hC₁ hG hs hs1 hb hl hx hl1 hmu hy ?_
  rw [← rootHt_affine]
  linarith [hIcc.1]

theorem i5_of_hasRef_of_refLower : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
    (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → (∀ c, RefLower (R c)) → T.I5 II := by
  intro Ψ _ _ N T II R hII hRef hLow
  obtain ⟨C, s₀, hs₀, hR⟩ := hRef
  choose Cf hCf1 hCf using hLow
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = ∑ c, Cf c := ⟨_, rfl⟩
  have hCfle : ∀ c, Cf c ≤ C₁ := fun c => by
    rw [hC₁def]
    exact Finset.single_le_sum (f := Cf) (fun c _ => by linarith [hCf1 c]) (Finset.mem_univ c)
  have hC₁1 : 1 ≤ C₁ := le_trans (hCf1 (Classical.arbitrary T.Comp)) (hCfle _)
  intro c₀ hc₀
  obtain ⟨θ₁, hθ₁, -, hθ⟩ := GlobalTheory.T.dominant_weight_gap_shift Ψ N T.j T.nu c₀ T.j_pos T.j_lt hc₀
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = (Fintype.card Ψ * N : ℝ) * 2 := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = C₁ + |C| * (G + 2) + 1 := ⟨_, rfl⟩
  have hCG : 0 ≤ |C| * (G + 2) := mul_nonneg (abs_nonneg C) (by linarith)
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK : 0 ≤ D * Real.log D + 2 + D := by
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ D) (Real.log_nonneg hD1)
    linarith
  refine ⟨min θ₁ (min 1 s₀), lt_min hθ₁ (lt_min one_pos hs₀),
    2 * D + (D * Real.log D + 2 + D) / Real.log 2, ?_⟩
  intro B hB c lam θ s hrat hlam hθpos hθle hsθ hgap hcg W hW
  have hθ1 : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθone : θ ≤ 1 := hθle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθs₀ : θ ≤ s₀ := hθle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hdom, hnorm, -⟩ := hθ lam θ hlam hθpos hθ1 hgap hcg
  have hspos : (0 : ℝ) < s := by rw [hsθ]; exact pow_pos hθpos 2
  have hs1 : (s : ℝ) ≤ 1 := by rw [hsθ]; exact pow_le_one₀ hθpos.le hθone
  have hss₀ : (s : ℝ) ≤ s₀ := by
    have h1 := mul_le_mul_of_nonneg_right hθone hθpos.le
    rw [hsθ, sq]
    linarith
  have hmu_eq : T.lamS lam s = lam - θ ^ 2 • T.nu := by unfold RootTower.lamS; rw [hsθ]
  have hdom' : Dominant (T.lamS lam s) := hmu_eq ▸ hdom
  have hnorm' : ‖T.lamS lam s‖ ≤ 2 := hmu_eq ▸ hnorm
  obtain ⟨i, u, hClose, hArch⟩ := hR B hB c
  have hA := hArch (T.lamS lam s) s hdom' hnorm' hspos hss₀
  have hl1 : l1 (T.lamS lam s) ≤ G := by
    refine (l1_le_card_mul_norm _).trans ?_
    rw [hGdef]
    exact mul_le_mul_of_nonneg_left hnorm' (by positivity)
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hBl : Real.log 2 ≤ Real.log B := Real.log_le_log two_pos hB2
  have hl : Real.log (1 / (s : ℝ)) = -Real.log s := by rw [one_div, Real.log_inv]
  have hlog1s : 0 ≤ Real.log (1 / (s : ℝ)) := by
    rw [hl]; linarith [Real.log_nonpos hspos.le hs1]
  have hRef' : ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (R c).P,
      -C₁ ≤ rootHt (R c) 1 0 1 L w ∧
      -(C₁ * Real.log (2 + C₁ + rootHt (R c) 1 0 1 L w)) - C₁ ≤ rootHt (R c) 1 (T.lamS lam s) 0 L w := by
    intro L _ _ w hw
    obtain ⟨h1, h2⟩ := hCf c L w hw
    have h3 := h2 (T.lamS lam s) hdom' hnorm'
    refine ⟨by linarith [hCfle c], ?_⟩
    have hx2 : 0 < 2 + Cf c + rootHt (R c) 1 0 1 L w := by linarith [hCf1 c]
    have hlg1 : 0 ≤ Real.log (2 + Cf c + rootHt (R c) 1 0 1 L w) := Real.log_nonneg (by linarith [hCf1 c])
    have hlg2 : Real.log (2 + Cf c + rootHt (R c) 1 0 1 L w) ≤ Real.log (2 + C₁ + rootHt (R c) 1 0 1 L w) :=
      Real.log_le_log hx2 (by linarith [hCfle c])
    have hm : Cf c * Real.log (2 + Cf c + rootHt (R c) 1 0 1 L w) ≤
        C₁ * Real.log (2 + C₁ + rootHt (R c) 1 0 1 L w) :=
      mul_le_mul (hCfle c) hlg2 hlg1 (by linarith)
    linarith [hCfle c]
  obtain ⟨x, hx, hbound⟩ := point_bound (C := C) (C₁ := C₁) (G := G) (t := scale s) (s := s)
    (b := Real.log B) (l := Real.log (1 / (s : ℝ))) hII (T.M B c) (R c) i u (T.lamS lam s) hC₁1 hG0 hspos hs1
    hlogB.le hlog1s hl1 hRef' hClose hA hW
  rw [← hDdef] at hbound
  unfold RootTower.mbarHt
  refine le_trans ?_ hbound
  have hDC : C₁ + 1 ≤ D := by rw [hDdef]; linarith
  have hy0 : 0 < 2 + D + x := by linarith
  have hDpos : 0 < D := by linarith
  have hz := Real.log_le_sub_one_of_pos (div_pos (mul_pos hspos hy0) hDpos)
  rw [Real.log_div (mul_pos hspos hy0).ne' hDpos.ne', Real.log_mul hspos.ne' hy0.ne'] at hz
  have hyb : D * Real.log (2 + D + x) ≤ (s : ℝ) * x + (s : ℝ) * (2 + D) - D + D * Real.log D
      + D * Real.log (1 / (s : ℝ)) := by
    have e : D * ((s : ℝ) * (2 + D + x) / D - 1) = (s : ℝ) * x + (s : ℝ) * (2 + D) - D := by
      rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hDpos.ne']
      ring
    have hm := mul_le_mul_of_nonneg_left hz hDpos.le
    rw [e] at hm
    have e2 : D * (Real.log (s : ℝ) + Real.log (2 + D + x) - Real.log D) =
        D * Real.log (s : ℝ) + D * Real.log (2 + D + x) - D * Real.log D := by ring
    have e3 : D * Real.log (1 / (s : ℝ)) = -(D * Real.log (s : ℝ)) := by rw [hl]; ring
    linarith
  have hs2D : (s : ℝ) * (2 + D) ≤ 2 + D := mul_le_of_le_one_left (by linarith) hs1
  have hlogBs : Real.log (B / (s : ℝ)) = Real.log B + Real.log (1 / (s : ℝ)) := by
    rw [Real.log_div (show (0:ℝ) < B by linarith).ne' hspos.ne', hl]
    ring
  rw [hlogBs]
  have hdivge : D * Real.log D + 2 + D ≤
      (D * Real.log D + 2 + D) / Real.log 2 * (Real.log B + Real.log (1 / (s : ℝ))) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left (by linarith) hK
  have e4 : (2 * D + (D * Real.log D + 2 + D) / Real.log 2) * (Real.log B + Real.log (1 / (s : ℝ))) =
      2 * (D * Real.log B) + 2 * (D * Real.log (1 / (s : ℝ))) +
        (D * Real.log D + 2 + D) / Real.log 2 * (Real.log B + Real.log (1 / (s : ℝ))) := by ring
  rw [e4]
  have h5 := mul_nonneg hDpos.le hlogB.le
  have h6 := mul_nonneg hDpos.le hlog1s
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.RefTower
