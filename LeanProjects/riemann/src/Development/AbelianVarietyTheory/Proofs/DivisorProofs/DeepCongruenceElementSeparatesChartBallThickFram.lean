import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantChartPointCentreFactorTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThickPointHyperbolic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

noncomputable section

namespace GlobalTheory.ThickSep

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates Module Submodule
open scoped ComplexConjugate Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def scl (X : Data E r) (s : X.Ψ → ℝ) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun u τ := ((s τ : ℝ) : ℂ) • u τ
  map_add' u v := by funext τ; simp [smul_add]
  map_smul' c u := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact smul_comm ((s τ : ℝ) : ℂ) c (u τ)

theorem gI_scl (X : Data E r) (x : Frame X.Ψ r) (s t : X.Ψ → ℝ) (u v : X.Ψ → Fin r → ℂ) :
    MajorantOperators.gI x (scl X s u) (scl X t v) = ∑ τ, s τ * t τ * (X.Hf x τ (u τ) (v τ)).re := by
  unfold MajorantOperators.gI
  refine Finset.sum_congr rfl fun τ _ => ?_
  show (X.Hf x τ (((s τ : ℝ) : ℂ) • u τ) (((t τ : ℝ) : ℂ) • v τ)).re = _
  rw [UnipotentCoefficientShift.Hf_smul_left, UnipotentCoefficientShift.Hf_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul]

def Qf (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) : ℝ :=
  ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)

theorem firstMinimumSq_le_weightedMajorantQuadraticForm (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {w : Fin r → E}
    (hw : w ∈ X.Λ) (hw0 : w ≠ 0) : X.firstMinimumSq x ≤ Qf X x w := by
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw, hw0, rfl⟩
  rintro _ ⟨u, -, -, rfl⟩
  exact Finset.sum_nonneg fun τ _ =>
    mul_nonneg (TwoSidedBoostBounds.c_pos X τ).le (MajorantOperators.maj_nonneg hx τ _)

theorem Hf_refl_self (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : Fin r → ℂ) :
    (X.Hf x τ ((2 : ℂ) • X.jp x τ a) ((2 : ℂ) • X.jp x τ a)).re = 4 * X.maj x τ a := by
  rw [UnipotentCoefficientShift.Hf_smul_right, UnipotentCoefficientShift.Hf_smul_left, Data.Hf_eq_jp, X.hermC_jp_jp hx,
    ← Data.Hf_eq_jp, X.Hf_self hx, show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
  simp
  ring

theorem exists_short (X : Data E r) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (hsd : EqCovol.IsSelfDualTr X) (hl : 0 < X.firstMinimumSq x) :
    ∃ v : Fin (2 * fdeg E * r) → Fin r → E, (∀ i, v i ∈ X.Λ) ∧ LinearIndependent ℚ v ∧
      ∃ φ : (Fin r → E) →+ EuclideanSpace ℝ (Fin (2 * fdeg E * r)),
        (∀ u, ‖φ u‖ ^ 2 = Qf X x u) ∧
        ∀ i, ‖φ (v i)‖ ^ 2 ≤ (((2 * fdeg E * r : ℕ) : ℝ) ^ 2 / √(X.firstMinimumSq x)) ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := ShortVectors.exists_basis X.Λ X.Λ_fg X.Λ_span
  have hcard : Fintype.card X.Ψ = fdeg E := QuadraticCoefficientForms.card_Psi (X := X)
  have hfr : finrank ℝ (X.Ψ → Fin r → ℂ) = 2 * fdeg E * r := by
    rw [Module.finrank_pi_fintype, ← hcard]
    simp [Module.finrank_pi_fintype]
    ring
  obtain ⟨θ, hθ⟩ := ThickPoint.exists_euclidean_real hfr (ThickPoint.majForm X x hx)
    ⟨fun u v => MajorantOperators.gI_comm hx u v⟩ (fun u => by
      rw [ThickPoint.majForm_apply, MajorantOperators.gI_self hx]
      exact Finset.sum_nonneg fun τ _ => MajorantOperators.maj_nonneg hx τ _)
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => TwoSidedBoostBounds.c_pos X τ
  let sc : X.Ψ → ℝ := fun τ => √(X.c τ)
  let si : X.Ψ → ℝ := fun τ => (√(X.c τ))⁻¹
  have hss : ∀ τ, sc τ * si τ = 1 := fun τ =>
    mul_inv_cancel₀ (Real.sqrt_pos.2 (hc τ)).ne'
  have hsc : ∀ τ, sc τ * sc τ = X.c τ := fun τ => Real.mul_self_sqrt (hc τ).le
  have hsi : ∀ τ, si τ * si τ = (X.c τ)⁻¹ := fun τ => by
    simp only [si, ← mul_inv, Real.mul_self_sqrt (hc τ).le]
  let φ : (Fin r → E) →+ EuclideanSpace ℝ (Fin (2 * fdeg E * r)) :=
    ((θ.comp (scl X sc)).toAddMonoidHom).comp (ThickPoint.embHom X)
  let ψ : (Fin r → E) →+ EuclideanSpace ℝ (Fin (2 * fdeg E * r)) :=
    ((θ.comp (scl X si)).toAddMonoidHom).comp (ThickPoint.reflHom X x)
  have hφψ : ∀ u w, inner ℝ (φ u) (ψ w) = (ThickPoint.traceFormOf X.Gm u w : ℝ) := by
    intro u w
    show inner ℝ (θ (scl X sc _)) (θ (scl X si _)) = _
    rw [hθ, ThickPoint.majForm_apply, gI_scl, ← ThickPoint.pair_eq X x hx u w]
    unfold MajorantOperators.gI
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hss, one_mul]
  have hφ : ∀ u, ‖φ u‖ ^ 2 = Qf X x u := by
    intro u
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (θ (scl X sc _)) (θ (scl X sc _)) = _
    rw [hθ, ThickPoint.majForm_apply, gI_scl]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hsc]
    show X.c τ * (X.Hf x τ (Data.emb τ.1 u) (Data.emb τ.1 u)).re = _
    rw [X.Hf_self hx, Complex.ofReal_re]
  have hψ : ∀ w, ‖ψ ((-X.ξ0) • w)‖ ^ 2 = Qf X x w := by
    intro w
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (θ (scl X si _)) (θ (scl X si _)) = _
    rw [hθ, ThickPoint.majForm_apply, gI_scl]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hsi]
    show (X.c τ)⁻¹ * (X.Hf x τ ((2 : ℂ) • X.jp x τ (Data.emb τ.1 ((-X.ξ0) • w)))
      ((2 : ℂ) • X.jp x τ (Data.emb τ.1 ((-X.ξ0) • w)))).re = _
    rw [Hf_refl_self X hx]
    have he : Data.emb τ.1 ((-X.ξ0) • w) = (τ.1 (-X.ξ0)) • Data.emb τ.1 w := by
      funext a; simp [Data.emb]
    rw [he, UnipMove.DeltaValuation.maj_smul, Complex.normSq_eq_norm_sq, map_neg, norm_neg]
    have hcτ : X.c τ = 2 * ‖τ.1 X.ξ0‖ := rfl
    have h0 := hc τ
    rw [hcτ] at h0 ⊢
    field_simp
    ring
  obtain ⟨v, hv, hli, hle⟩ := ThickPoint.transference_pair b (ThickPoint.traceFormOf X.Gm)
    (ThickPoint.traceFormOf_isSymm X.Gm_herm) (ThickPoint.traceFormOf_nondegenerate X.Gm_herm X.Gm_det)
    φ ψ hφψ (√(X.firstMinimumSq x)) (Real.sqrt_pos.2 hl) (by
      intro u hu hk
      have hξ : -X.ξ0 ≠ 0 := neg_ne_zero.2 X.ξ0_ne
      obtain ⟨w, rfl⟩ : ∃ w, u = (-X.ξ0) • w :=
        ⟨(-X.ξ0)⁻¹ • u, by rw [smul_smul, mul_inv_cancel₀ hξ, one_smul]⟩
      have hw0 : w ≠ 0 := by rintro rfl; exact hu (smul_zero _)
      have hw : w ∈ X.Λ := by
        refine (hsd w).2 fun y hy => ?_
        obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).2 hy)
        choose k hk using hk
        refine ⟨∑ j, c j * k j, ?_⟩
        rw [← HermitianTraceFormVanishing.herm_smul_left, ← ThickPoint.traceFormOf_apply, map_sum]
        simp only [map_zsmul, hk]
        simp
      rw [Real.sq_sqrt hl.le, hψ]
      exact firstMinimumSq_le_weightedMajorantQuadraticForm X hx hw hw0)
  exact ⟨v, fun i => (hb _).1 (hv i), hli, φ, hφ, hle⟩

theorem maj_le_four (X : Data E r) {x : Frame X.Ψ r} (hx : ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) {z z' : V (nd X)}
    (hz : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100) (hz' : (r : ℝ) ^ 2 * ‖z'‖ ≤ 1 / 100)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X x z) = rmul (cpt X x z') b) (τ : X.Ψ) (v : Fin r → E) :
    X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) ≤
      4 * X.maj x τ (Data.emb τ.1 v) := by
  have h1 := (GlobalTheory.ChartGraph.maj_cpt_le_two E r X x z' hx hz' τ
    (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v))).2
  have h2 := (GlobalTheory.ChartGraph.maj_cpt_le_two E r X x z hx hz τ (Data.emb τ.1 v)).1
  have e1 : X.maj (cpt X x z') τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) =
      X.maj (cpt X x z) τ (Data.emb τ.1 v) := by
    rw [← GlobalTheory.ChartMult.maj_rmul_any X _ hb, ← heq, GlobalTheory.ChartMult.emb_mulVec',
      GlobalTheory.MajInv.maj_lact X hγ]
  rw [e1] at h1
  linarith

theorem Qf_le_four (X : Data E r) {x : Frame X.Ψ r} (hx : ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x)
    {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) {z z' : V (nd X)}
    (hz : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100) (hz' : (r : ℝ) ^ 2 * ‖z'‖ ≤ 1 / 100)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X x z) = rmul (cpt X x z') b) (v : Fin r → E) :
    Qf X x ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ≤ 4 * Qf X x v := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have := mul_le_mul_of_nonneg_left (maj_le_four X hx hγ hz hz' hb heq τ v)
    (TwoSidedBoostBounds.c_pos X τ).le
  linarith

theorem Qf_nsmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (M : ℕ) (w : Fin r → E) :
    Qf X x (M • w) = (M : ℝ) ^ 2 * Qf X x w := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have he : Data.emb τ.1 (M • w) = ((M : ℝ) : ℂ) • Data.emb τ.1 w := by
    funext a; simp [Data.emb, nsmul_eq_mul]
  rw [he, UnipotentCoefficientShift.maj_smul hx]
  ring

theorem deep_cong_chart_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (M : ℕ) (x : Frame X.Ψ r), GlobalTheory.EqCovol.IsSelfDualTr X → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → 100 * ((X.Ψ.card : ℝ) * r) ^ 4 ≤ (M : ℝ) * X.firstMinimumSq x → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec v - v = M • w) → ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1 := by
  intro E _ _ _ r X M x hsd hx hM γ hγ hcong z z' hz hz' b hb heq
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  have hdom : x ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X hx
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hsm : ∀ w : V (nd X), ‖w‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → (r : ℝ) ^ 2 * ‖w‖ ≤ 1 / 100 := by
    intro w hw
    calc (r : ℝ) ^ 2 * ‖w‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = 1 / 100 := by field_simp
  have hcard : (X.Ψ.card : ℝ) = fdeg E := by
    rw [← QuadraticCoefficientForms.card_Psi (X := X), Fintype.card_coe]
  have hf : (1 : ℝ) ≤ fdeg E := by
    have := QuadraticCoefficientForms.card_Psi_pos (X := X)
    rw [QuadraticCoefficientForms.card_Psi (X := X)] at this
    exact_mod_cast this
  set P : ℝ := (fdeg E : ℝ) * r with hP
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  rw [hcard] at hM
  have hP4 : 1 ≤ P ^ 4 := one_le_pow₀ hP1
  have hla : 0 < X.firstMinimumSq x := by
    by_contra h
    push_neg at h
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg M) h
    nlinarith
  obtain ⟨v, hvΛ, hli, φ, hφ, hvs⟩ := exists_short X x hdom hsd hla
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v i ≠ v i := by
    by_contra hall
    push_neg at hall
    apply hne
    have hcv : Fintype.card (Fin (2 * fdeg E * r)) = finrank ℚ (Fin r → E) := by
      rw [Fintype.card_fin, Module.finrank_pi_fintype, ShortVectors.finrank_eq]
      simp
      ring
    have hfN : 0 < fdeg E := by
      have := QuadraticCoefficientForms.card_Psi_pos (X := X)
      rwa [QuadraticCoefficientForms.card_Psi (X := X)] at this
    haveI : Nonempty (Fin (2 * fdeg E * r)) := ⟨⟨0, by positivity⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli hcv
    have hlin : (Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars ℚ =
        LinearMap.id := B.ext fun j => by
      simp [B, hall j]
    refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun y => ?_))
    have := LinearMap.congr_fun hlin y
    simpa using this
  obtain ⟨w, hwΛ, hw⟩ := hcong (v i) (hvΛ i)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [smul_zero, sub_eq_zero] at hw
    exact hi hw
  have h1 : (M : ℝ) ^ 2 * X.firstMinimumSq x ≤ ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i - v i)‖ ^ 2 := by
    rw [hφ, hw, Qf_nsmul X hdom]
    exact mul_le_mul_of_nonneg_left (firstMinimumSq_le_weightedMajorantQuadraticForm X hdom hwΛ hw0) (by positivity)
  have h2 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i)‖ ≤ 2 * ‖φ (v i)‖ := by
    have h := Qf_le_four X hx hγ (hsm z hz) (hsm z' hz') hb heq (v i)
    rw [← hφ, ← hφ] at h
    have : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i)‖ ^ 2 ≤ (2 * ‖φ (v i)‖) ^ 2 := by
      rw [mul_pow]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  have h3 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i - v i)‖ ≤ 3 * ‖φ (v i)‖ := by
    rw [map_sub]
    have := norm_sub_le (φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i)) (φ (v i))
    linarith
  have h4 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v i - v i)‖ ^ 2 ≤ 9 * ‖φ (v i)‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [mul_pow] at this
    linarith
  have h5 := hvs i
  have hK : (((2 * fdeg E * r : ℕ) : ℝ) ^ 2 / √(X.firstMinimumSq x)) ^ 2 = 16 * P ^ 4 / X.firstMinimumSq x := by
    rw [div_pow, Real.sq_sqrt hla.le, hP]
    push_cast
    ring
  rw [hK] at h5
  have h6 : (M : ℝ) ^ 2 * X.firstMinimumSq x ≤ 9 * (16 * P ^ 4 / X.firstMinimumSq x) := by linarith
  have h7 : ((M : ℝ) * X.firstMinimumSq x) ^ 2 ≤ 144 * P ^ 4 := by
    have := mul_le_mul_of_nonneg_right h6 hla.le
    rw [mul_assoc 9, div_mul_cancel₀ _ hla.ne'] at this
    nlinarith
  have h8 : (100 * P ^ 4) ^ 2 ≤ ((M : ℝ) * X.firstMinimumSq x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hM 2
  nlinarith

end GlobalTheory.ThickSep
