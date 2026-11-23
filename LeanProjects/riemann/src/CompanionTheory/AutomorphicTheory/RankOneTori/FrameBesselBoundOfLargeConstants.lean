import CompanionTheory.AutomorphicTheory.RankOneTori.Factor
import CompanionTheory.AutomorphicTheory.RankOneTori.BeRankScale
import CompanionTheory.AutomorphicTheory.RankOneTori.NzTranslate
import CompanionTheory.AutomorphicTheory.RankOneTori.KDense
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OneBesselTor
import Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf Formalism.FourierDecayAlt Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.L2.SG.Pf.OBT Formalism.BasicNotions
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

set_option maxHeartbeats 1600000 in
theorem gap_arith (hk : 1 ≤ k) {C : ℝ} (hC : 100 ≤ C) :
    ThreeDimData.GapOK k r (C * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
    Pv.AmpDD.GapCell k r (C * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hne : n = 2 * r + k + 1 := by rw [hn]; push_cast; ring
  set m : ℝ := 2 * ((r : ℝ) + 1) with hm
  have hme : ((2 * r + 2 : ℕ) : ℝ) = m := by rw [hm]; push_cast; ring
  have hm2 : 2 ≤ m := by linarith
  have hmn : m ≤ n := by linarith
  set s := Real.sqrt m with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hpow : m ^ ((9 : ℝ) / 2) = m ^ 4 * s := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    norm_num
  set X : ℝ := ((3 * (r + 1) : ℕ) : ℝ) * n ^ 2 + n ^ 3 with hX
  have hn1 : 1 ≤ n := by linarith
  have hXn : n ^ 3 ≤ X := by rw [hX]; exact le_add_of_nonneg_left (by positivity)
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ hn1
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  set Y : ℝ := m ^ 2 * n ^ 3 with hY
  have hY4 : 4 * n ^ 3 ≤ Y := mul_le_mul_of_nonneg_right hm4 (by positivity)
  have ha : ThreeDimData.aOf r (C * m ^ ((9 : ℝ) / 2) * X) = C * m ^ 4 * X / 8 := by
    unfold ThreeDimData.aOf
    rw [hpow, ← hm, ← hs]
    field_simp
  have hbig : 400 * Y ≤ C * m ^ 4 * X := by
    have e1 : 4 * Y ≤ m ^ 4 * X := by
      calc 4 * Y ≤ m ^ 2 * Y := mul_le_mul_of_nonneg_right hm4 (by positivity)
        _ = m ^ 4 * n ^ 3 := by rw [hY]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hXn (by positivity)
    calc 400 * Y = 100 * (4 * Y) := by ring
      _ ≤ C * (m ^ 4 * X) := mul_le_mul hC e1 (by positivity) (by linarith)
      _ = _ := by ring
  have hdN : ThreeDimData.dN k r ≤ n ^ 2 := by unfold ThreeDimData.dN; rw [hne]; nlinarith
  have hdN0 : 0 ≤ ThreeDimData.dN k r := by unfold ThreeDimData.dN; nlinarith
  have hAS : ThreeDimData.AS k r ≤ n ^ 3 := by
    unfold ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) ≤ n := by push_cast; linarith
    calc _ ≤ n * n ^ 2 := mul_le_mul this hdN hdN0 (by linarith)
      _ = _ := by ring
  have hAS0 : 0 ≤ ThreeDimData.AS k r := mul_nonneg (Nat.cast_nonneg _) hdN0
  have hAG : ThreeDimData.AG k r ≤ 4 * n ^ 3 := by
    unfold ThreeDimData.AG
    have : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ n * n := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have e : n ^ 2 = n * n := by ring
    calc _ = 4 * (((k : ℝ) + r) * ((r : ℝ) + 1)) := by ring
      _ ≤ _ := by linarith
  have hAG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hM : ThreeDimData.Mexp r ≤ m ^ 2 / 2 := by
    have e : m ^ 2 / 2 = 2 * ((r : ℝ) ^ 2 + r + 1) + 2 * r := by rw [hm]; ring
    unfold ThreeDimData.Mexp
    linarith
  have h1 : 2 * ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 5 * Y := by
    calc _ ≤ m ^ 2 * (5 * n ^ 3) := mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = _ := by rw [hY]; ring
  have h2 : 9 * ((r : ℝ) + 1) * n ^ 2 ≤ 9 * n ^ 3 := by
    have : ((r : ℝ) + 1) * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc _ = 9 * (((r : ℝ) + 1) * n ^ 2) := by ring
      _ ≤ 9 * (n * n ^ 2) := by linarith
      _ = _ := by ring
  have h3 : 10 * ((r : ℝ) + 1) ^ 2 * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 50 * Y / 4 := by
    have e : 10 * ((r : ℝ) + 1) ^ 2 = 10 * m ^ 2 / 4 := by rw [hm]; ring
    calc _ ≤ 10 * m ^ 2 / 4 * (5 * n ^ 3) := by
          rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [hY]; ring
  rw [hme]
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · rw [hpow]
    have : C * m ^ 4 * X ≤ C * (m ^ 4 * s) * X := by
      have h0 : 0 ≤ C * m ^ 4 * X := by linarith
      calc _ ≤ C * m ^ 4 * X * s := le_mul_of_one_le_right h0 hs1
        _ = _ := by ring
    linarith
  · rw [ha]; linarith
  · rw [ha]; linarith
  · unfold Pv.AmpDD.GapCell
    rw [ha]; linarith

theorem exists_low {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ) : ∃ w : H, IsLowUnitH k r ε lam σ w := by
  obtain ⟨A, hA, -, -, -, -, -, ⟨S, hS⟩, -⟩ := h
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, A, hA, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · exact Submodule.smul_mem _ _ (le_sSup (s := {S | IsKTypeOf ε _ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS hvS)

theorem kfin_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {y : H}
    (hy : IsKFinHpk (k := k) (r := r) σ y) (a : ℂ) : IsKFinHpk (k := k) (r := r) σ (a • y) := by
  obtain ⟨S, h1, h2, h3⟩ := hy
  exact ⟨S, h1, S.smul_mem a h2, h3⟩

theorem rankOne_core (hKD : Pv.AmpDD.KDense) (L : LocBessel k r) {κ₀ h : ℝ} (hκ₀ : 0 < κ₀) (hc : L.c = cOfDpsi (κ₀ : ℂ))
    (h0 : L.κN ≠ 0) (h1 : L.κN ≠ ⊤) (hg : Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h) (hO : ThreeDimData.GapOK k r h)
    (hC : Pv.AmpDD.GapCell k r h) :
    ∃ (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (Ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ) (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj k r κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0) := by
  classical
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hc0 : L.c ≠ 0 := by
    rw [hc, cOfDpsi]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hκ₀.ne')
  obtain ⟨l, hl⟩ := be_rank_scale hO.1 L.hlam hσ hg hO.2.1 L.hz.1 L.hz.2 L.hπ L.hμW.1 h0 h1 hκ₀
  obtain ⟨l', hl'⟩ := be_rank_scale hO.1 L.hlam hσ hg hO.2.1 L.hz'.1 L.hz'.2 L.hπ' L.hμW'.1 h0 h1 hκ₀
  rw [← hc] at hl hl'
  obtain ⟨w0, hw0⟩ := exists_low L.hσ
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hKS := CompanionTheory.D.gk.admitted.k_finite_smooth k r L.ε L.lam L.Hs L.σ L.hlam hσ
  have hw0s := hKS w0 hw0K
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    obtain ⟨_, _, hw⟩ := hw0
    have hnorm : ‖w0‖ = 1 := hw.1
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  set Sm := PI.UpqRep.smoothVecs (k := k) (r := r) L.σ with hSm
  have hdec : ∀ v ∈ Sm, ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C * B.gN g ^ (-(ThreeDimData.aOf r h - 1)) := by
    obtain ⟨C, Ws, -, hb⟩ := CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range k r L.ε L.lam h L.Hs L.σ L.hlam hσ hg hO w0 hw0K
    intro v hv
    refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v‖).sum, fun g hgU => ?_⟩
    have := hb v hv g⁻¹ (WeylGroupFacts.uh_inv hgU)
    rw [((P.norm_inverse_bound k r).2 g hgU).1] at this
    rw [P.MatrixMultiplicationContinuity.sigma_inner hσ hgU, norm_inner_symm, neg_sub]
    exact this
  have key := fun (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r))
      (hcell : Cell L (ThreeDimData.aOf r h - 1) γ μR ν) =>
    cell_factor L hw1 l l' Sm hdec (fun v hv t ht => hl _ (P.TranslationBesselVanishing.smooth_translate hσ hw0s ht) v hv)
      (fun v hv t ht => hl' _ (P.TranslationBesselVanishing.smooth_translate hσ hw0s ht) v hv) hcell
  have key2 : ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)), ∃ Ψ : L.Wq →L[ℂ] L.Wp,
      ∀ μR, Cell L (ThreeDimData.aOf r h - 1) γ μR ν → ∀ (A : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs),
      (∀ x, ContinuousLinearMap.adjoint A x ∈ Sm) → (∀ w, Q w ∈ Sm) → ∀ F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp),
      (∀ x ∈ UH (Hpk k r), F x = A.comp ((L.σ x).comp Q)) → OrbInt L F γ ν = (lamP L l A * lamQ L l' Q) • Ψ := by
    intro γ ν
    by_cases hex : ∃ μR, Cell L (ThreeDimData.aOf r h - 1) γ μR ν
    · obtain ⟨μR, hμ⟩ := hex
      obtain ⟨Ψ, hΨ⟩ := key γ μR ν hμ
      exact ⟨Ψ, fun _ _ => hΨ⟩
    · exact ⟨0, fun μR hμ => absurd ⟨μR, hμ⟩ hex⟩
  choose Ψ hΨ using key2
  have hdata : ∀ (A : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs), (∀ x, ContinuousLinearMap.adjoint A x ∈ Sm) →
      (∀ w, Q w ∈ Sm) → ∀ F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), (∀ x ∈ UH (Hpk k r), F x = A.comp ((L.σ x).comp Q)) →
      HasBData L F (lamP L l A * lamQ L l' Q) (fun g => Ψ g (pairMeas L)) Ψ := fun A Q hA hQ F hF =>
    ⟨fun c μ hc' hμ => hΨ _ _ _ (cell_big hO.1 L h0 h1 hC c μ hc' hμ) A Q hA hQ F hF,
      fun γ g μR ν hG a1 a2 a3 a4 => hΨ _ _ _ (cell_small L hc0 h1 hO hC hG a1 a2 a3 a4) A Q hA hQ F hF⟩
  have hadj : ∀ {κ τ : ℝ}, 0 < κ → 0 < τ → ∀ (A : L.Hs →L[ℂ] L.Wp) (x : L.Wp),
      ContinuousLinearMap.adjoint (A.comp (L.σ (dMi k r κ τ))) x =
        L.σ (dM k r κ τ) (ContinuousLinearMap.adjoint A x) := by
    intro κ τ hκ hτ A x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      P.MatrixMultiplicationContinuity.sigma_inner hσ (dMi_mem_UH hκ hτ), dMi_inv hκ hτ]
  refine ⟨fun g => Ψ g (pairMeas L), Ψ, fun A Q => lamP L l A * lamQ L l' Q,
    fun A Q κ τ => lamP L l (A.comp (L.σ (dMi k r κ τ))) * lamQ L l' ((L.σ (dM k r κ τ)).comp Q),
    fun A Q hAQ => hdata A Q (fun x => hKS _ (hAQ.2 x)) (fun w => hKS _ (hAQ.1 w)) _ fun _ _ => rfl,
    fun A Q κ τ hκ hτ hAQ => hdata _ _ (fun x => ?_) (fun w => ?_) _ fun x hx => ?_, fun κ τ hκ hτ A Q hAQ hne => ?_⟩
  · rw [hadj hκ hτ]
    exact P.TranslationBesselVanishing.smooth_translate hσ (hKS _ (hAQ.2 x)) (dM_mem_UH hκ hτ)
  · exact P.TranslationBesselVanishing.smooth_translate hσ (hKS _ (hAQ.1 w)) (dM_mem_UH hκ hτ)
  · show A.comp ((L.σ (dMi k r κ τ * x * dM k r κ τ)).comp Q) = _
    rw [P.TranslationBesselVanishing.sigma_mul hσ (WeylGroupFacts.uh_mul (dMi_mem_UH hκ hτ) hx) (dM_mem_UH hκ hτ),
      P.TranslationBesselVanishing.sigma_mul hσ (dMi_mem_UH hκ hτ) hx]
    rfl
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hne)
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hne)
    obtain ⟨y, hy, hy1, hy2⟩ := side_nz hKD L.hlam hσ hg hO hw0 L.hz.1 L.hz.2 hc0 L.hπ L.hμW.1 L.hμW.2 h0 h1 hl
      (hAQ.2 _) (fun h => hi (by rw [h, inner_zero_left])) (dM_mem_UH hκ hτ)
    obtain ⟨y', hy', hy1', hy2'⟩ := side_nz hKD L.hlam hσ hg hO hw0 L.hz'.1 L.hz'.2 hc0 L.hπ' L.hμW'.1 L.hμW'.2 h0 h1 hl'
      (hAQ.1 _) (fun h => hj (by rw [h, inner_zero_right])) (dM_mem_UH hκ hτ)
    set ξ := l (L.σ (dM k r κ τ) y) with hξ
    set ξ' := l' (L.σ (dM k r κ τ) y') with hξ'
    have ha : ∀ x : L.Wp, ContinuousLinearMap.adjoint ((innerSL ℂ y).smulRight ξ) x = ⟪ξ, x⟫_ℂ • y := fun x => by
      refine ext_inner_left ℂ fun w => ?_
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    refine ⟨(innerSL ℂ y).smulRight ξ, (innerSL ℂ ξ').smulRight y', ⟨fun w => kfin_smul hy' _, fun x => ?_⟩,
      mul_ne_zero ?_ ?_⟩
    · rw [ha]; exact kfin_smul hy _
    · simp only [lamP, hadj hκ hτ, ha, map_smul, hy2, inner_smul_left, inner_conj_symm]
      simp only [mul_comm ⟪stdOrthonormalBasis ℂ L.Wp _, ξ⟫_ℂ]
      rw [OrthonormalBasis.sum_inner_mul_inner]
      exact inner_self_ne_zero.2 hy1
    · simp only [lamQ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
        hy2', inner_smul_right]
      rw [OrthonormalBasis.sum_inner_mul_inner]
      exact inner_self_ne_zero.2 hy1'

theorem rankOneTor_of_kDense (hKD : Pv.AmpDD.KDense) (D : D7) {Cgf : ℝ} (hC : 100 ≤ Cgf) : RankOneTor D Cgf := by
  intro L κ₀ hκ₀ hc h0 h1 _ hg
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨a1, a2⟩ := gap_arith (r := D.R.rS) hk hC
  exact rankOne_core hKD L hκ₀ hc h0.ne' h1 hg a1 a2

theorem k_finite_dense : Pv.AmpDD.KDense := KD.kDense

theorem rank_one_torus_bound (D : D7) {Cgf : ℝ} (hC : 100 ≤ Cgf) : RankOneTor D Cgf := rankOneTor_of_kDense k_finite_dense D hC

theorem one_bessel_torus_bound (D : D7) {Cgf : ℝ} (hC : 100 ≤ Cgf) : OneBesselTor D Cgf :=
  oneBesselTor_of_rankOne D Cgf (rank_one_torus_bound D hC)

end Formalism.MainStatements.RankOne
