import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundSmoothDecayingCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableEmptyWordDensityDecayingCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompExpIteratedDerivBounded
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NeZeroOfIsLocPt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem dom_pow_le (G : ℝ) (hG : 0 < G) (m q : ℕ) (h : m ≤ q) : G ^ m ≤ 1 + G ^ q := by
  rcases le_total G 1 with h1 | h1
  · have := pow_le_one₀ (n := m) hG.le h1
    have := pow_pos hG q
    linarith
  · have := pow_le_pow_right₀ h1 h
    linarith

theorem dom_real_bound {ι κ : Type} [Fintype ι] [Fintype κ] (E Ct n D G C S C' : ℝ) (L a p₀ : ℕ)
    (u : ι → ℝ) (v : κ → ℝ) (hCt : 0 ≤ Ct) (hn : 0 ≤ n) (hD : 0 < D) (hG : 0 < G) (hC : 0 ≤ C)
    (hS0 : 0 ≤ S) (hS : S ≤ C' * G ^ p₀) (hu0 : ∀ e, 0 ≤ u e) (hv0 : ∀ t, 0 ≤ v t)
    (hL : L * (1 + 2 * a) ≤ 2 * p₀)
    (hu : ∀ e, u e ≤ C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * S * ∑ t, v t)
    (hE : E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2) :
    E ≤ (Ct * Fintype.card ι * (C * C') ^ 2 * Fintype.card κ) *
      ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hL
  have hT0 : 0 ≤ ∑ t, v t := Finset.sum_nonneg fun t _ => hv0 t
  have hT : (∑ t, v t) ^ 2 ≤ Fintype.card κ * ∑ t, v t ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := v)
  have hV0 : 0 ≤ ∑ t, v t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have h1 : ∑ e, u e ^ 2 ≤ Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
    have : ∀ e ∈ (Finset.univ : Finset ι),
        u e ^ 2 ≤ (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
      intro e _
      refine pow_le_pow_left₀ (hu0 e) ((hu e).trans ?_) 2
      gcongr
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  have h2 : (D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2 = G ^ m := by
    have e : (G ^ p₀) ^ 2 = G ^ L * (G ^ (a * L)) ^ 2 * G ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [mul_comm p₀ 2, hm]; ring
    rw [mul_pow, e, div_pow, inv_pow, inv_pow, ← pow_mul D 2 L, mul_comm 2 L, pow_mul D L 2]
    have := pow_pos hD L
    have := pow_pos hG L
    have := pow_pos hG (a * L)
    field_simp
  have h3 : G ^ m ≤ 1 + (G ^ p₀) ^ 2 := by
    rw [← pow_mul]
    exact dom_pow_le G hG _ _ (by omega)
  have h4 : ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) = n * (1 + (G ^ p₀) ^ 2) * ∑ t, v t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  calc E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2 := hE
    _ ≤ Ct * n * (D ^ 2 / G) ^ L *
        (Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2) := by gcongr
    _ = Ct * n * Fintype.card ι * (C * C') ^ 2 *
        ((D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2) * (∑ t, v t) ^ 2 := by ring
    _ ≤ Ct * n * Fintype.card ι * (C * C') ^ 2 * (1 + (G ^ p₀) ^ 2) * (Fintype.card κ * ∑ t, v t ^ 2) := by
        rw [h2]; gcongr
    _ = _ := by rw [h4]; ring

theorem dom_thr (Cc r k : ℝ) (N L : ℝ) (hCc : 8 ≤ Cc) (hr : 0 ≤ r) (hk : 0 ≤ k) (hL : L ≤ N) (hN : 0 ≤ N) :
    L * (8 * (r + 1) * (2 * r + k + 1)) ≤ Cc * (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2) := by
  have h1 : r + 1 ≤ (r + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : 2 * r + k + 1 ≤ (2 * r + k + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc L * (8 * (r + 1) * (2 * r + k + 1)) ≤ N * (Cc * (r + 1) ^ 4 * (2 * r + k + 1) ^ 2) := by
        have : 0 ≤ Cc := by linarith
        gcongr
    _ = _ := by ring

theorem top_density_dominated : GlobalTheory.HCXi.BesselXiIntegrable → ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) (w : List C.Letter), C6.IsCut0 χ → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) → N * (1 + 2 * a P.r) ≤ 2 * p₀ → KB.CutWord P p.l0 w → w.length ≤ N → (∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ ε : ℝ, 0 < ε → ∀ c₀ : Fin (P.r + 1) → ℂ, ‖(fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) c₀‖ ≤ h c₀ := by
  intro hXi a ha Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.wordBound_smooth_decaying_coefficients a ha Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.integrable_emptyWordDensity_decayingCoefficients hXi
  refine ⟨max C1 (max C2 8), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N w hχ hDD hf hfA hth hN hw hwN
  have hc1 : C1 ≤ max C1 (max C2 8) := le_max_left _ _
  have hc2 : C2 ≤ max C1 (max C2 8) := (le_max_left _ _).trans (le_max_right _ _)
  have hc8 : 8 ≤ max C1 (max C2 8) := (le_max_right _ _).trans (le_max_right _ _)
  generalize max C1 (max C2 8) = Cc at hth hc1 hc2 hc8
  obtain ⟨C, J, Θs, hC, hpoly, hb⟩ := h1 Wp Wq P p N w hDD hw hwN
  obtain ⟨hcut, C', hC', hld⟩ := ld_cut_pow χ p₀ J hχ
  obtain ⟨Ct, hCt, htop⟩ := GlobalTheory.TopDensityBound.top_density_le Wp Wq P p w
  constructor
  · intro ε hε
    have hs := (GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P p.T.base p₀ 0 _ f A₀ (hcut ε hε) hf (hfA 0)).1
    have hm := GlobalTheory.TopVec.aestronglyMeasurable_tv Wp Wq P p Cb _ w hDD hw hs
    simp only [GlobalTheory.TopVec.Ew_eq_norm_tv_sq]
    exact hm.norm.pow 2
  have hth1 : C1 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (2 * (P.r : ℝ) + 2) * p₀ := by
    refine le_trans ?_ (hth.trans (le_of_eq (by push_cast; ring)))
    gcongr
  set d : ℝ := ((w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) with hd
  have hth2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    have e1 := dom_thr Cc P.r P.k N w.length hc8 (by positivity) (by positivity) (by exact_mod_cast hwN) (by positivity)
    have e2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤
        Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by gcongr
    have e3 : d = (w.length : ℝ) * (8 * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1)) := by
      rw [hd]; push_cast; ring
    rw [mul_add] at hth
    linarith
  have hΘ : ∀ t : Fin Θs.length, B.CkOn ⊤ (B.GV P.k P.r) (B.opApply Θs[t.1] f) ∧
      ∀ m : ℕ, B.InCC (A₀ - d) m (B.opApply Θs[t.1] f) := fun t =>
    Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq _ d A₀ (by positivity)
      ((polyOp_ok P.k P.r Wp Wq _ _ _ (hpoly _ (List.getElem_mem t.2))).2.1 d le_rfl) f hf hfA
  refine ⟨fun c => (Ct * Fintype.card (Ix (Fin w.length)) * (C * ((J + 1) * C')) ^ 2 * Fintype.card (Fin Θs.length)) *
    ∑ t : Fin Θs.length, (TBB.Ew p (fun _ => 1) (B.opApply Θs[t.1] f) (P.r + 1) [] (TBB.bigPt P.r c) +
      TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Θs[t.1] f g)
        (P.r + 1) [] (TBB.bigPt P.r c)), ?_, ?_⟩
  · refine Integrable.const_mul (integrable_finset_sum _ fun t _ => Integrable.add ?_ ?_) _
    · refine h2 Wp Wq P p _ (A₀ - d) (hΘ t).1 (hΘ t).2 (hth2.trans ?_)
      have : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by positivity
      linarith
    · exact h2 Wp Wq P p _ _ (Formalism.FourierDecayAlt.P.CutBP.ckOn_Gpow_smul _ _ p₀ (hΘ t).1)
        (Formalism.FourierDecayAlt.P.CutBP.inCC_Gpow_smul _ _ p₀ (hΘ t).2) hth2
  intro ε hε c
  beta_reduce
  by_cases hc : (∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [(htop _ c).1 hc, norm_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
      add_nonneg (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _) (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _))
  obtain ⟨hc0, hG⟩ := hc
  obtain ⟨hn, -, hE⟩ := (htop (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) c).2 hc0 hG
  have hGp : ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) (TBB.bigPt P.r c) =
        ((TBB.Gp p (TBB.bigPt P.r c) ^ p₀ : ℝ) : ℂ) • p.V F (TBB.bigPt P.r c) := by
    intro F
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · exact Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p F p₀ hl hG
    · rw [Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), smul_zero]
  simp only [fun H => ((htop H c).2 hc0 hG).2.1, hGp, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  rw [Real.norm_eq_abs]
  refine dom_real_bound _ Ct _ ‖∏ l, c l‖ _ C
    (∑ j ∈ Finset.range (J + 1), |LE.ld j (fun y => χ (y / ε) * y ^ p₀) (TBB.Gp p (TBB.bigPt P.r c))|) _
    w.length (a P.r) p₀ _ (fun t : Fin Θs.length => ‖B.hsVec (p.V (B.opApply Θs[t.1] f) (TBB.bigPt P.r c))‖)
    hCt hn (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun l _ => hc0 l)) hG hC
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((Nat.mul_le_mul_right _ hwN).trans hN) ?_ hE
  · have := Finset.sum_le_card_nsmul (Finset.range (J + 1)) _ _ fun j hj =>
      hld ε _ hε hG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    simpa [mul_assoc] using this
  · intro e
    have := hb _ f ⟨p₀, A₀, hcut ε hε, hf, hfA, hth1⟩ e c hc0 hG
    rwa [← Fin.sum_univ_fun_getElem] at this

end GlobalTheory.HatNF
