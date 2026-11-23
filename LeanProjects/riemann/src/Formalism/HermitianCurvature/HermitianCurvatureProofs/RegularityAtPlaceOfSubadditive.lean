import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample

namespace Formalism.FourierDecayAlt.P.TBBx4

open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate

noncomputable section

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

lemma hsVec_normSq (Y : Wq →L[ℂ] Wp) :
    ‖B.hsVec Y‖ ^ 2 = ∑ i, ‖Y (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

lemma hsVec_normSq_adj (Y : Wq →L[ℂ] Wp) :
    ‖B.hsVec Y‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by
  rw [hsVec_normSq]
  calc ∑ i, ‖Y (stdOrthonormalBasis ℂ Wq i)‖ ^ 2
      = ∑ i, ∑ j, ‖inner ℂ (stdOrthonormalBasis ℂ Wp j) (Y (stdOrthonormalBasis ℂ Wq i))‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => ((stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right _).symm
    _ = ∑ j, ∑ i, ‖inner ℂ (stdOrthonormalBasis ℂ Wq i)
          ((ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j))‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_right _

lemma hs_le_of_adj (X : Wq →L[ℂ] Wp) (A A' : Wq →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by
  rw [hsVec_normSq_adj, hsVec_normSq_adj, hsVec_normSq_adj, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  exact h _

lemma hs_comp_le (X : Wq →L[ℂ] Wp) (A : Wq →L[ℂ] Wq) :
    ‖B.hsVec (X.comp A)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [hsVec_normSq_adj, hsVec_normSq_adj, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint.norm_map A, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2

lemma hsVec_real_smul_sq (x : ℝ) (Y : Wq →L[ℂ] Wp) :
    ‖B.hsVec ((x : ℂ) • Y)‖ ^ 2 = x ^ 2 * ‖B.hsVec Y‖ ^ 2 := by
  rw [hsVec_normSq, hsVec_normSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

end hs

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

lemma ew_not_loc (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ D.IsLocPt γ (P.r + 1)) : Ew p (fun _ => 1) F (P.r + 1) [] γ = 0 := by
  unfold Ew NP KB.Pl.RR D.RRplace
  rw [dif_neg (fun h => hγ h.1)]
  simp

lemma V_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ (D.IsLocPt γ (P.r + 1) ∧ 0 < Gp p γ)) : p.V F γ = 0 := by
  unfold KB.Pl.V D.vecV
  exact dif_neg hγ

lemma ew_zero_of (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ (D.IsLocPt γ (P.r + 1) ∧ 0 < Gp p γ)) : Ew p (fun _ => 1) F (P.r + 1) [] γ = 0 := by
  by_cases hl : D.IsLocPt γ (P.r + 1)
  · rw [TBBx2.Tri.Ew_top p F hl, V_zero p F hγ, TBBx2.Tri.hsVec_zero]
    simp
  · exact ew_not_loc p F hl

lemma ew_nonneg (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt) :
    0 ≤ Ew p (fun _ => 1) F (P.r + 1) [] γ := by
  by_cases hl : D.IsLocPt γ (P.r + 1)
  · rw [TBBx2.Tri.Ew_top p F hl]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _)
  · rw [ew_not_loc p F hl]

lemma Gp_le (p : KB.Pl P Wp Wq) (γ : C.LPt) : Gp p γ ≤ ‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2 := by
  have hT : 0 ≤ TTp p := (mul_pos p.T.base.T_pos p.T.base.T'_pos).le
  have e := Complex.normSq_eq_norm_sq (D.ptMatN γ (P.r + 1)).det
  have h0 := Complex.normSq_nonneg (D.ptMatN γ P.r).det
  unfold Gp D.ptG
  nlinarith [mul_nonneg hT h0]

theorem orbJ_smul_ae {k r : ℕ} (Ds : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (F G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ) (hc : c ≠ 0)
    (hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds γ G q = c • D.orbIntegrand Ds γ F q) :
    D.orbJ Ds γ μR G = c • D.orbJ Ds γ μR F := by
  classical
  have hP : (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ G q) Ds.μSS) =
      (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ F q) Ds.μSS) := by
    funext θ
    apply propext
    refine and_congr_right fun _ => ?_
    rw [integrable_congr (hae.mono fun q hq => by
      show θ q • D.orbIntegrand Ds γ G q = c • (θ q • D.orbIntegrand Ds γ F q)
      rw [hq, smul_comm])]
    exact integrable_fun_smul_iff hc _
  unfold D.orbJ
  simp only [smul_dite, smul_zero]
  refine TBBx2.choose_dite_congr (E := Wq →L[ℂ] Wp) _ _ hP
    (fun θ => ∫ q, θ q • D.orbIntegrand Ds γ G q ∂Ds.μSS)
    (fun θ => c • ∫ q, θ q • D.orbIntegrand Ds γ F q ∂Ds.μSS) fun θ _ => ?_
  rw [← integral_smul]
  exact integral_congr_ae (hae.mono fun q hq => by
    show θ q • D.orbIntegrand Ds γ G q = c • (θ q • D.orbIntegrand Ds γ F q)
    rw [hq, smul_comm])

theorem vec_Gpow (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) {γ : C.LPt}
    (_hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ) :
    p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) γ =
      ((Gp p γ ^ p₀ : ℝ) : ℂ) • p.V F γ := by
  have hc : ((Gp p γ ^ p₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hG p₀).ne'
  unfold KB.Pl.V D.vecV
  split_ifs with h1 h2
  · apply orbJ_smul_ae _ _ _ _ _ _ hc
    filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
    have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = Gp p γ := by
      rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
      rfl
    unfold D.orbIntegrand B.rho
    simp only [hGq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rw [smul_comm]
  · simp
  · simp

end place

section norm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem normAt_of_pts (p : KB.Pl P Wp Wq) (f Fp Fm : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Ap Am : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ)
    (hVp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V Fp γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (Ap γ))
    (hVm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V Fm γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (Am γ))
    (hlow : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (Ap γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (Am γ)) v‖ ^ 2))
    (hnp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖Ap γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (hnm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖Am γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀) :
    NormAt p f Fp Fm b n₀ p₀ := by
  constructor
  · intro γ hγ hG
    rw [TBBx2.Tri.Ew_top p f hγ, TBBx2.Tri.Ew_top p Fp hγ, TBBx2.Tri.Ew_top p Fm hγ, hVp γ hγ hG, hVm γ hγ hG,
      hsVec_real_smul_sq, hsVec_real_smul_sq]
    have hl := hs_le_of_adj (p.V f γ) (Ap γ) (Am γ) _ (hlow γ hγ hG)
    set n := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)
    have hn : 0 ≤ n := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    set K := (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀
    have hGp : (Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2 = 1 := by
      rw [← pow_mul, inv_pow, mul_comm p₀ 2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hG.ne')
    calc n * ‖B.hsVec (p.V f γ)‖ ^ 2
        ≤ n * (K * (‖B.hsVec ((p.V f γ).comp (Ap γ))‖ ^ 2 + ‖B.hsVec ((p.V f γ).comp (Am γ))‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hl hn
      _ = K * (Gp p γ)⁻¹ ^ (2 * p₀) *
            (n * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (Ap γ))‖ ^ 2) +
              n * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (Am γ))‖ ^ 2)) := by
          have e : K * (Gp p γ)⁻¹ ^ (2 * p₀) *
              (n * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (Ap γ))‖ ^ 2) +
                n * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (Am γ))‖ ^ 2)) =
              n * (K * (‖B.hsVec ((p.V f γ).comp (Ap γ))‖ ^ 2 + ‖B.hsVec ((p.V f γ).comp (Am γ))‖ ^ 2)) *
                ((Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2) := by ring
          rw [e, hGp, mul_one]
  · intro c F hF
    have hF' : F = Fp ∨ F = Fm := by simpa using hF
    have hT : 0 < Tq p := p.T.base.T'_pos
    by_cases hγ : D.IsLocPt (bigPt P.r c) (P.r + 1) ∧ 0 < Gp p (bigPt P.r c)
    · obtain ⟨hl, hG⟩ := hγ
      obtain ⟨A, hVF, hA⟩ : ∃ A : Wq →L[ℂ] Wq, p.V F (bigPt P.r c) =
          ((Gp p (bigPt P.r c) ^ p₀ : ℝ) : ℂ) • (p.V f (bigPt P.r c)).comp A ∧
          ‖A‖ ^ 2 ≤ (Gp p (bigPt P.r c) / Tq p) ^ n₀ := by
        rcases hF' with rfl | rfl
        · exact ⟨_, hVp _ hl hG, hnp _ hl hG⟩
        · exact ⟨_, hVm _ hl hG, hnm _ hl hG⟩
      rw [TBBx2.Tri.Ew_top p F hl, TBBx2.Tri.Ew_top p f hl, hVF, hsVec_real_smul_sq]
      set n := Real.sqrt (nPt P.k P.r (TTp p) (bigPt P.r c)) * Real.sqrt (nPt P.k P.r (TTp p) (bigPt P.r c))
      have hn : 0 ≤ n := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      set g := Gp p (bigPt P.r c)
      set X := B.hsVec (p.V f (bigPt P.r c))
      set d := ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖
      have hgd : g ≤ d ^ 2 := Gp_le p (bigPt P.r c)
      have h1 : ‖B.hsVec ((p.V f (bigPt P.r c)).comp A)‖ ^ 2 ≤ (g / Tq p) ^ n₀ * ‖X‖ ^ 2 :=
        (hs_comp_le _ A).trans (mul_le_mul_of_nonneg_right hA (sq_nonneg _))
      have h2 : (g ^ p₀) ^ 2 * (g / Tq p) ^ n₀ ≤ (d ^ 2) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ := by
        have e : (g ^ p₀) ^ 2 * (g / Tq p) ^ n₀ = g ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ := by
          rw [div_eq_mul_inv, mul_pow, ← pow_mul, pow_add, mul_comm p₀ 2]
          ring
        rw [e]
        gcongr
      calc n * ((g ^ p₀) ^ 2 * ‖B.hsVec ((p.V f (bigPt P.r c)).comp A)‖ ^ 2)
          ≤ n * ((g ^ p₀) ^ 2 * ((g / Tq p) ^ n₀ * ‖X‖ ^ 2)) := by gcongr
        _ = ((g ^ p₀) ^ 2 * (g / Tq p) ^ n₀) * (n * ‖X‖ ^ 2) := by ring
        _ ≤ ((d ^ 2) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀) * (n * ‖X‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg hn (sq_nonneg _))
        _ = d ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ * (n * ‖X‖ ^ 2) := by rw [pow_mul]
    · rw [ew_zero_of p F hγ]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (ew_nonneg p f _)

def fpm (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : B.Mat P.k P.r → (Wq →L[ℂ] Wq)) (p₀ : ℕ) :
    B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (A g)

theorem normAt_fpm (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq)) (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ)
    (hAp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ))
    (hAm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ))
    (hlow : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2))
    (hnp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (hnm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀) :
    NormAt p f (fpm p f Ap p₀) (fpm p f Am p₀) b n₀ p₀ := by
  exact normAt_of_pts p f _ _ ApPt AmPt b n₀ p₀
    (fun γ hγ hG => (vec_Gpow p (fun g => (f g).comp (Ap g)) p₀ hγ hG).trans (by rw [hAp γ hγ hG]))
    (fun γ hγ hG => (vec_Gpow p (fun g => (f g).comp (Am g)) p₀ hγ hG).trans (by rw [hAm γ hγ hG]))
    hlow hnp hnm

end norm

section reg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

lemma pt_bound (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {n : ℕ}
    (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ) (a : ℕ) (γ : C.LPt)
    (hexp : D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      ((D.ptMatN γ (P.r + 1)).det ^ a) • p.V f γ = ∑ i, co i • p.V (fi i) γ) :
    ‖(D.ptMatN γ (P.r + 1)).det‖ ^ (2 * a) * Ew p (fun _ => 1) f (P.r + 1) [] γ ≤
      (∑ i, ‖co i‖) * ∑ i, ‖co i‖ * Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ := by
  have hS : 0 ≤ ∑ i, ‖co i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  by_cases hγ : D.IsLocPt γ (P.r + 1) ∧ 0 < Gp p γ
  · obtain ⟨hl, hG⟩ := hγ
    simp only [TBBx2.Tri.Ew_top p _ hl]
    set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)
    have hn : 0 ≤ nn := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    set d := (D.ptMatN γ (P.r + 1)).det
    set x : Fin n → ℝ := fun i => ‖B.hsVec (p.V (fi i) γ)‖
    have htri : ‖d‖ ^ a * ‖B.hsVec (p.V f γ)‖ ≤ ∑ i, ‖co i‖ * x i := by
      have e : B.hsVec ((d ^ a) • p.V f γ) = ∑ i, co i • B.hsVec (p.V (fi i) γ) := by
        rw [hexp hl hG, TBBx2.Tri.hsVec_sum]
        exact Finset.sum_congr rfl fun i _ => TBBx2.Tri.hsVec_smul _ _
      have e2 : ‖B.hsVec ((d ^ a) • p.V f γ)‖ = ‖d‖ ^ a * ‖B.hsVec (p.V f γ)‖ := by
        rw [TBBx2.Tri.hsVec_smul, norm_smul, norm_pow]
      rw [← e2, e]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i _ => norm_smul _ _
    have hsq : (‖d‖ ^ a * ‖B.hsVec (p.V f γ)‖) ^ 2 ≤ (∑ i, ‖co i‖ * x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) htri 2
    have hcs := TBBx2.Tri.cs_bound (fun i => ‖co i‖) x (fun i => norm_nonneg _)
    have e3 : ‖d‖ ^ (2 * a) * (nn * ‖B.hsVec (p.V f γ)‖ ^ 2) = nn * (‖d‖ ^ a * ‖B.hsVec (p.V f γ)‖) ^ 2 := by
      rw [mul_comm 2 a, pow_mul]
      ring
    have e4 : (∑ i, ‖co i‖) * ∑ i, ‖co i‖ * (nn * x i ^ 2) =
        nn * ((∑ i, ‖co i‖) * ∑ i, ‖co i‖ * x i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3, e4]
    exact mul_le_mul_of_nonneg_left (hsq.trans hcs) hn
  · rw [ew_zero_of p f hγ, mul_zero]
    exact mul_nonneg hS (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (ew_nonneg p _ _))

theorem regularity_at_place_of_expansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ)
    (hb : 0 ≤ b)
    (hexp : ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
      ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
      (∀ i, jN2 p (fi i) ≤ jN2 p f) ∧
      (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] (bigPt P.r c))) ∧
      ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (bigPt P.r c) (P.r + 1) → 0 < Gp p (bigPt P.r c) →
        ((D.ptMatN (bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (bigPt P.r c) =
          ∑ i, co i • p.V (fi i) (bigPt P.r c)) :
    RegularityBoundBigCell p f b C₃ a₁ := by
  intro a ha
  obtain ⟨n, fi, co, hsum, hj, hmeas, hE⟩ := hexp a ha
  set S := ∑ i, ‖co i‖ with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  set B₀ := b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ))
  have hB₀ : b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) = B₀ ^ 2 := by
    rw [show 2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ) = C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ) * 2 by ring,
      Real.rpow_mul hb, Real.rpow_two]
  have hpt : ∀ c : Fin (P.r + 1) → ℂ,
      ENNReal.ofReal (‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * a) *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) ≤
      ENNReal.ofReal S * ∑ i, ENNReal.ofReal ‖co i‖ *
        ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] (bigPt P.r c)) := by
    intro c
    refine (ENNReal.ofReal_le_ofReal (pt_bound p f fi co a _ (hE c))).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hS, ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (norm_nonneg _) (ew_nonneg p _ _))]
    congr 1
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (norm_nonneg _)
  unfold bigCellDetWeightedEnergyIntegral
  calc ∫⁻ c, ENNReal.ofReal (‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * a) *
          Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c))
      ≤ ∫⁻ c, ENNReal.ofReal S * ∑ i, ENNReal.ofReal ‖co i‖ *
          ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] (bigPt P.r c)) := lintegral_mono hpt
    _ = ENNReal.ofReal S * ∑ i, ENNReal.ofReal ‖co i‖ * jN2 p (fi i) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun i _ => (hmeas i).const_mul _]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
    _ ≤ ENNReal.ofReal S * ∑ i, ENNReal.ofReal ‖co i‖ * jN2 p f := by
        gcongr with i
        exact hj i
    _ = ENNReal.ofReal (S * S) * jN2 p f := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _), ← mul_assoc,
          ← ENNReal.ofReal_mul hS]
    _ ≤ ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ))) * jN2 p f := by
        rw [hB₀]
        gcongr
        rw [sq]
        exact mul_le_mul hsum hsum hS (hS.trans hsum)

end reg

section iter

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def mulD (r : ℕ) : Module.End ℂ ((Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) where
  toFun x := fun c => (D.ptMatN (bigPt r c) (r + 1)).det • x c
  map_add' x y := by
    funext c
    simp [smul_add]
  map_smul' z x := by
    funext c
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

end iter

end

end Formalism.FourierDecayAlt.P.TBBx4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

theorem norm_bound_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ)
    (hAp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ))
    (hAm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ))
    (hlow : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (TBB.Tq p / TBB.Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2))
    (hnp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀)
    (hnm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀) :
    Formalism.FourierDecayAlt.TBB.NormAt p f (TBBx4.fpm p f Ap p₀) (TBBx4.fpm p f Am p₀) b n₀ p₀ := TBBx4.normAt_fpm p f Ap Am ApPt AmPt b n₀ p₀ hAp hAm hlow hnp hnm

theorem regularity_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (hb : 0 ≤ b)
    (hexp : ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
      ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
      (∀ i, TBB.jN2 p (fi i) ≤ TBB.jN2 p f) ∧
      (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fi i) (P.r + 1) [] (TBB.bigPt P.r c))) ∧
      ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
        ((D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (TBB.bigPt P.r c) =
          ∑ i, co i • p.V (fi i) (TBB.bigPt P.r c)) :
    Formalism.FourierDecayAlt.TBB.RegularityBoundBigCell p f b C₃ a₁ := TBBx4.regularity_at_place_of_expansion p f b C₃ a₁ hb hexp

end Formalism.FourierDecayAlt.P
