import CompanionTheory.AutomorphicTheory.BesselWaveGrids.SpanBall
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.EigStrOfMem
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.ProductMoment
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.BigCellDerivativeExpansionOfIsDSOfCoefOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors

noncomputable section

namespace CompanionTheory.WaveGrid.WAt

open MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants CompanionTheory.WaveGrid CompanionTheory.WaveGrid.SpanBall
open CompanionTheory.WaveGrid.MomL (mnr momL ew_sum_le)
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT KDecay Wsp Letters IsCoef wsp_orth gap_of_box CoefCC CoefEig PhZero BetaInfZero)
open scoped InnerProductSpace ENNReal

def UniqG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), IsHCParam lam →
    ∀ h : ℝ, GapAtLeast ε lam h → ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 + 1 < h →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r ε lam σ →
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : B.Mat k r → (H' →L[ℂ] H')),
      PI.UpqRep.IsDSHpk k r ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UH (Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

section one

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem kfin_map {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] {σ : B.Mat k r → (H →L[ℂ] H)} {σ' : B.Mat k r → (H' →L[ℂ] H')} (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ UH (Hpk k r), ∀ x, U (σ g x) = σ' g (U x)) {v : H} (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) :
    PI.UpqRep.IsKFinHpk (k := k) (r := r) σ' (U v) := by
  obtain ⟨S, hS, hvS, hst⟩ := hv
  refine ⟨S.map U.toLinearEquiv.toLinearMap, inferInstance, Submodule.mem_map_of_mem hvS, ?_⟩
  rintro g hg _ ⟨x, hx, rfl⟩
  exact ⟨σ g x, hst g hg x hx, hU g hg.1 x⟩

theorem coefOf_of_wsp (hU : UniqG) (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (hg : GapAtLeast ε μ h) (hh : ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 + 1 < h) (R : BranchingSupport.Rep k r) (hR : R.IsDS ε μ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) : BallW.CoefOf R F := by
  have key : ∃ (ι : Type) (_ : Fintype ι) (x y : ι → R.H) (X : ι → (Wq →L[ℂ] Wp)),
      (∀ i, x i ∈ R.TK ∧ y i ∈ R.TK) ∧ ∀ g ∈ B.GV k r, F g = ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i := by
    have hTK := (GlobalTheory.rep_basic_of_isDS hK k r ε μ R hR).2.2.2.2.2.2.1
    induction hF using Submodule.span_induction with
    | mem F h' =>
      obtain ⟨φ, T, ⟨H, i1, i2, i3, σ, v, w, -, hσ, hv, hw, hφ⟩, rfl⟩ := h'
      obtain ⟨U, hUσ⟩ := hU k r ε μ hR.1 h hg hh H σ hσ R.H R.σ hR.2
      refine ⟨Unit, inferInstance, fun _ => U w, fun _ => U v, fun _ => T,
        fun _ => ⟨hTK _ (kfin_map U hUσ hw), hTK _ (kfin_map U hUσ hv)⟩, fun g hg => ?_⟩
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hφ g hg, ← hUσ g hg, U.inner_map_map]
    | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, Empty.elim, fun i => i.elim, fun g _ => by simp⟩
    | add F F' _ _ h h' =>
      obtain ⟨ι, _, x, y, X, h1, h2⟩ := h
      obtain ⟨ι', _, x', y', X', h1', h2'⟩ := h'
      refine ⟨ι ⊕ ι', inferInstance, Sum.elim x x', Sum.elim y y', Sum.elim X X', ?_, fun g hg => ?_⟩
      · rintro (i | i)
        exacts [h1 i, h1' i]
      · rw [Fintype.sum_sum_type, Pi.add_apply, h2 g hg, h2' g hg]
        rfl
    | smul c F _ h =>
      obtain ⟨ι, _, x, y, X, h1, h2⟩ := h
      refine ⟨ι, inferInstance, x, y, fun i => c • X i, h1, fun g hg => ?_⟩
      rw [Pi.smul_apply, h2 g hg, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  obtain ⟨ι, _, x, y, X, h1, h2⟩ := key
  intro l l'
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, Fintype.card ι, fun i => x (e i), fun i => y (e i), fun i => X (e i), fun i => h1 _, fun g hg => ?_, rfl⟩
  rw [h2 g hg]
  exact (Equiv.sum_comp e fun i => ⟪x i, R.σ g (y i)⟫_ℂ • X i).symm

theorem bound_of_inCC {A : ℝ} {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : B.InCC A m F) :
    ContinuousOn F (B.GV k r) ∧ ∃ c, 0 ≤ c ∧ ∀ g ∈ B.GV k r, ‖F g‖ ≤ c * B.gN g ^ (-A) := by
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨GlobalTheory.CoefZero.continuousOn_of_ckOn hc1, max c 0, le_max_right _ _, fun g hg => ?_⟩
  have h1 : B.gN g ^ A * ‖F g‖ ≤ c := hc2 [] [] (by simp) (by simp) (by simp) g hg
  have hp := BetaSesquilinearity.gN_pos hg
  rw [Real.rpow_neg hp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hp _), mul_comm]
  exact h1.trans (le_max_left _ _)

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem normSq_eq (hk : 2 ≤ k) (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A 5 F) : B.normSq D F = ENNReal.ofReal (B.beta D F F).re := by
  obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := b_any_of_xi k r Wp Wq D A hA
  obtain ⟨c, hc⟩ := JCx2.sq_inCC_mono le_rfl (by norm_num : 4 ≤ 5) hF
  have hfin := (hC F F c c hF hF hc hc).1
  set g : (Fin r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _)
  have hJ : StronglyMeasurable fun q : (Fin r → ℂ) × ℂ => B7.JM D F (1, 1) q :=
    (B7.sm_JM D (bound_of_inCC hF).1).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin r → ℂ) × ℂ => ‖B7.hsL (B7.JM D F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hgm : Measurable g := by
    have e : g = fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B7.hsL (B7.JM D F (1, 1) q)‖ ^ 2 := by
      funext q
      by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
      · simp only [hg, hw, zero_mul]
      have hw' := hw
      unfold bcWeight at hw'
      split_ifs at hw' with hle
      · have hq : q ∈ B7.Q0 D := by
          refine ⟨fun a ha => left_ne_zero_of_mul hw' (Finset.prod_eq_zero (Finset.mem_univ a) ?_), ?_⟩
          · rw [ha, norm_zero, zero_pow]
            unfold Mdim
            have := a.isLt
            omega
          · refine hle.lt_or_eq.resolve_right fun h => right_ne_zero_of_mul hw' ?_
            rw [← h, sub_self, zero_pow (by omega)]
        rw [B7.JM_eq D F (1, 1) hq, bessel_function_trivial_index k r Wp Wq D F, B7.hsL_apply]
      · exact absurd rfl hw'
    rw [e]
    exact (B7.measurable_bcWeight _ _).mul (hN.pow_const 2)
  have hβ : B.beta D F F = ((∫ q, g q : ℝ) : ℂ) := by
    unfold B.beta betaBig
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    rw [inner_self_eq_norm_sq_to_K]
    push_cast [hg]
    rfl
  rw [hβ, Complex.ofReal_re, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
    hgm.aestronglyMeasurable]
  exact (ENNReal.ofReal_toReal hfin).symm

theorem normSq_le_sum (hk : 2 ≤ k) (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) {ι : Type} (S : Finset ι)
    (F : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ i ∈ S, B.InCC A 5 (F i))
    (ho : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → B.beta D (F i) (F j) = 0) {i : ι} (hi : i ∈ S) :
    B.normSq D (F i) ≤ B.normSq D (∑ j ∈ S, F j) := by
  classical
  have e : (∑ j ∈ S, F j) = fun g => ∑ j : S, F j g := by
    funext g
    rw [Finset.sum_apply, Finset.sum_coe_sort S (fun j => F j g)]
  have hS : B.InCC A 5 fun g => ∑ j : S, F j g := JCx2.sq_inCC_sum _ _ fun j _ => hF j j.2
  have h1 : ∀ j : S, B.beta D (fun g => ∑ l : S, F l g) (F j) = B.beta D (F j) (F j) := fun j => by
    have h := CutBP.beta_sum_left D hA (fun _ : S => (1 : ℂ)) (fun l : S => F l) (fun l => hF l l.2) (hF j j.2)
      Finset.univ
    simp only [one_smul, one_mul] at h
    exact h.trans (Finset.sum_eq_single j (fun l _ hl => ho l l.2 j j.2 fun e => hl (Subtype.ext e))
      fun h => absurd (Finset.mem_univ j) h)
  have h2 := (CutBP.beta_sum_right D hA (fun j : S => F j) (fun j => hF j j.2) hS Finset.univ).trans
    (Finset.sum_congr rfl fun j _ => h1 j)
  have h3 : ∀ j : S, 0 ≤ (B.beta D (F j) (F j)).re := fun j => by
    obtain ⟨t, ht, e⟩ := CutBP.beta_self_real D (F j)
    rw [e, Complex.ofReal_re]
    exact ht
  have h4 := normSq_eq hk D hA hS
  rw [h2, Complex.re_sum] at h4
  rw [e, h4, normSq_eq hk D hA (hF i hi)]
  have h5 := Finset.single_le_sum (f := fun j : S => (B.beta D (F j) (F j)).re) (fun j _ => h3 j)
    (Finset.mem_univ (⟨i, hi⟩ : S))
  exact ENNReal.ofReal_le_ofReal h5

end one

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem V_dmin (p : KB.Pl P Wp Wq) {f F₀ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (he : ∀ g ∈ B.GV P.k P.r, F₀ g = f g) {j : ℕ}
    (hj : j ≤ P.r) (a : ℕ) (γ : C.LPt) (h0 : mnr hj γ ^ a ≠ 0) :
    p.V (fun g => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ ^ a • F₀ g) γ = mnr hj γ ^ a • p.V f γ := by
  unfold KB.Pl.V D.vecV
  split_ifs with h1 h2
  · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ h0
    filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
    have hGq : Dmin P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) ⟨j + 1, by omega⟩ = mnr hj γ := by
      rw [BigCellZetaMinors.dmin_sgs _ hq]
      unfold Dmin mnr
      rw [h2.choose_spec.2.1]
    unfold D.orbIntegrand B.rho
    simp only [hGq, he _ (B7.sgs_mem p.T.base hq h2.choose_spec.1), ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
    rw [smul_comm]
  · simp
  · simp

theorem mnr_bigPt_ne {r j : ℕ} (hj : j ≤ r) (c : Fin (r + 1) → ℂ) (hc : D.IsLocPt (TBB.bigPt r c) (r + 1)) :
    mnr hj (TBB.bigPt r c) ≠ 0 := by
  unfold mnr
  rw [show D.ptMatN (TBB.bigPt r c) (r + 1) = _ from PBJ.Dens.ptMatN_bigPt c, PBM.hMat_one,
    Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun a _ =>
    (hc.1 (1, c _) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨_, rfl⟩)).2

end place

theorem V_sum : ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (A : ℝ), c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (ι : Type) (S : Finset ι) (F : ι → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (∀ i ∈ S, B.InCC A 5 (F i)) →
    ∀ γ, p.V (∑ i ∈ S, F i) γ = ∑ i ∈ S, p.V (F i) γ := by
  obtain ⟨c₃, H⟩ := PolTop.vector_valued_orbital_linear
  refine ⟨c₃, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p A hA ι S F hF γ
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := V_csmul p (fun _ => 0) 0 γ
    simp only [zero_smul] at this
    rw [Finset.sum_empty, Finset.sum_empty]
    exact this
  | insert i S hi ih =>
    have hS : B.InCC A 5 (∑ j ∈ S, F j) := by
      have := JCx2.sq_inCC_sum S F fun j hj => hF j (Finset.mem_insert_of_mem hj)
      convert this using 2 with g
      rw [Finset.sum_apply]
    obtain ⟨h1, c1, hc1, b1⟩ := bound_of_inCC (hF i (Finset.mem_insert_self _ _))
    obtain ⟨h2, c2, hc2, b2⟩ := bound_of_inCC hS
    have hpos : ∀ g ∈ B.GPos p.T.base, 0 ≤ B.gN g ^ (-A) := fun g hg => Real.rpow_nonneg (BetaSesquilinearity.gN_pos hg.1).le _
    have key := H P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ A hA (F i) (∑ j ∈ S, F j) (c1 + c2) (by linarith)
      (h1.mono fun g hg => hg.1) (h2.mono fun g hg => hg.1)
      (fun g hg => (b1 g hg.1).trans (mul_le_mul_of_nonneg_right (by linarith) (hpos g hg)))
      (fun g hg => (b2 g hg.1).trans (mul_le_mul_of_nonneg_right (by linarith) (hpos g hg))) 1 1
    simp only [one_smul] at key
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih fun j hj => hF j (Finset.mem_insert_of_mem hj)]
    exact key

theorem weighted : ∃ c₃ : ℝ, ∀ {t : ∀ n : ℕ, (Fin n → Bool) → ℝ}, ZuckT t → ZuckDualT t → PI.KFinSmooth → CoefCC →
    CoefEig → PhZero → BetaInfZero → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    [CompleteSpace Wp] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ε : Fin (2 * P.r + P.k + 1) → Bool)
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (j : ℕ) (hj : j ≤ P.r) (a : ℕ) (A h : ℝ) (K : C.LPt → ℝ≥0∞),
    KFinDSCoef ε lam f → PI.ZuckTensor.GapAtLeast ε lam h → t _ ε + 1 + 2 * (((P.r + 1) * a : ℕ) : ℝ) < h →
    KDecay P.k P.r ε A (h - 2 * (((P.r + 1) * a : ℕ) : ℝ)) → B.AB P.k P.r ≤ A →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
    (∀ ν ∈ ball _ ((P.r + 1) * a), ∀ F ∈ Wsp P.k P.r Wp Wq ε (fun s => lam s + (ν s : ℝ)),
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤ K γ * TBB.jN2 p F) →
    ENNReal.ofReal (‖mnr hj γ‖ ^ (2 * a) * TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤
      ENNReal.ofReal (((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ (2 * ((P.r + 1) * a))) * K γ * momL p f hj a := by
  obtain ⟨c₃, HV⟩ := V_sum
  refine ⟨c₃, ?_⟩
  intro t hZ hZd hK h4 h5 h6 h7 P Wp Wq _ _ _ _ _ _ _ p f ε lam j hj a A h K hf hg ht hD hA hA3 γ hγ hG hB
  classical
  by_cases h0 : mnr hj γ ^ a = 0
  · rw [two_mul, pow_add, ← norm_pow, h0]
    simp
  obtain ⟨F₀, hF₀, he⟩ := Coef.kfin_wsp hf
  set q : B.Mat P.k P.r → ℂ := fun g => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ ^ a with hq
  have hqL : q ∈ Letters P.k P.r ^ ((P.r + 1) * a) := by
    have h1 : (fun g : B.Mat P.k P.r => Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩) ∈
        Letters P.k P.r ^ (P.r + 1) :=
      CompanionTheory.LimBd.Main.letters_pow_mono (show j + 1 ≤ P.r + 1 by omega)
        (CompanionTheory.LimBd.Main.det_mem_pow _ fun a b => CompanionTheory.LimBd.Main.herm_letter _ _)
    rw [pow_mul]
    exact Submodule.pow_mem_pow _ h1 a
  obtain ⟨F, hF, hsum⟩ := mul_mem_sumOn hZ hZd hqL hg ht hF₀
  set S := ball (2 * P.r + P.k + 1) ((P.r + 1) * a) with hS
  have hgν : ∀ ν ∈ S, PI.ZuckTensor.GapAtLeast ε (fun s => lam s + (ν s : ℝ)) (h - 2 * (((P.r + 1) * a : ℕ) : ℝ)) :=
    fun ν hν => gap_of_box (lam := lam) (μ := fun s => lam s + (ν s : ℝ)) (c := (((P.r + 1) * a : ℕ) : ℝ)) (fun s => by simpa using abs_ball hν s) hg
      (by linarith)
  have hcc : ∀ ν ∈ S, B.InCC A 5 (F ν) := fun ν hν => w_inCC hK h4 hD (hgν ν hν) (hF ν) 5
  have hVd : ∀ γ', mnr hj γ' ^ a ≠ 0 → p.V (∑ ν ∈ S, F ν) γ' = mnr hj γ' ^ a • p.V f γ' := fun γ' h' => by
    rw [← hsum]
    exact V_dmin p he hj a γ' h'
  have hE : ∀ ν ∈ S, TBB.jN2 p (F ν) ≤ momL p f hj a := by
    intro ν hν
    have h1 := normSq_le_sum p.hl.2.2 p.T.base hA S F hcc (fun ν₁ h₁ ν₂ h₂ hne =>
      wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _ h₁) (hgν _ h₂) (fun e => hne (funext fun s => by
        have := congrFun e s
        simp only [add_right_inj, Int.cast_inj] at this
        exact this)) (hF _) (hF _)) hν
    rw [← GlobalTheory.T.jN2_eq_normSq_base, ← GlobalTheory.T.jN2_eq_normSq_base] at h1
    refine h1.trans (lintegral_mono fun c => ENNReal.ofReal_le_ofReal ?_)
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · have hne : mnr hj (TBB.bigPt P.r c) ^ a ≠ 0 := pow_ne_zero _ (mnr_bigPt_ne hj c hc.1)
      rw [TBBx2.Tri.Ew_top p _ hc.1, TBBx2.Tri.Ew_top p _ hc.1, hVd _ hne, TBBx2.Tri.hsVec_smul, norm_smul, norm_pow]
      refine le_of_eq ?_
      rw [mul_comm 2 a, pow_mul]
      ring
    · rw [TBBx4.ew_zero_of p _ hc, TBBx4.ew_zero_of p _ hc, mul_zero]
  have hpt := ew_sum_le p f S F (fun _ => 1) (mnr hj γ ^ a) γ fun _ _ => by
    rw [← hVd γ h0, HV P Wp Wq p A hA3 _ S F hcc γ]
    simp
  simp only [norm_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hpt
  rw [norm_pow, ← pow_mul, mul_comm a 2] at hpt
  have hcard : (S.card : ℝ) ≤ ((2 * (2 * P.r + P.k + 1) + 1 : ℕ) : ℝ) ^ ((P.r + 1) * a) := by
    exact_mod_cast card_ball _ _
  refine (ENNReal.ofReal_le_ofReal hpt).trans ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_sum_of_nonneg fun ν _ => TBBx4.ew_nonneg p _ _]
  have h2 : ∑ ν ∈ S, ENNReal.ofReal (TBB.Ew p (fun _ => 1) (F ν) (P.r + 1) [] γ) ≤
      ENNReal.ofReal (S.card : ℝ) * (K γ * momL p f hj a) := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun ν hν =>
      (hB ν hν _ (hF ν)).trans (mul_le_mul' le_rfl (hE ν hν))).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, ENNReal.ofReal_natCast]
  refine (mul_le_mul' le_rfl h2).trans ?_
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), two_mul ((P.r + 1) * a), pow_add]
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul hcard hcard (Nat.cast_nonneg _) (by positivity))) le_rfl) le_rfl

end CompanionTheory.WaveGrid.WAt
