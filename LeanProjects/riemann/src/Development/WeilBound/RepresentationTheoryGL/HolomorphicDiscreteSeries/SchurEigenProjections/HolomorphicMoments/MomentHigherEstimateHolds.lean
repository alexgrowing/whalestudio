import Development.WeilBound.CoreStatements.BranchingTraces.FormTSingle
import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.ComatrixWordBound
import Development.WeilBound.CoreStatements.BranchingTraces.CasimirDecomposition.UnitaryDecompositionExists
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.KFiniteWordBoundIndefUnitary
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.BigProjP

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace PositivityTheory.UnitaryDecomposition

open Formalism.REAL Formalism.MainNotions.S Formalism.MainNotions.BridgeCSchur CompanionTheory.D.Upq.Sm

def MomentHeA : Prop := ForPairs fun {n} ε lam ε' _ B e H H' _ _ _ _ _ _ π σ ν =>
  ∀ (P : H →L[ℂ] H') (w : H') (κ : ℝ), Intertw ε' e π σ P → ‖w‖ = 1 → ‖ContinuousLinearMap.adjoint P w‖ = 1 → 0 < κ →
    Integrable (fun h : UJ ε' => ⟪w, σ (um h) w⟫_ℂ) ν →
    (∀ x : UJ ε', ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * conj ⟪w, σ (um (h⁻¹ * x)) w⟫_ℂ ∂ν = κ * conj ⟪w, σ (um x) w⟫_ℂ) →
    (∃ η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π, ⟪η, ContinuousLinearMap.adjoint P w⟫_ℂ ≠ 0 ∧
      ∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (um h) w⟫_ℂ * ⟪η, π (emb e (um h)) a⟫_ℂ ∂ν =
        κ * (⟪η, ContinuousLinearMap.adjoint P w⟫_ℂ * ⟪ContinuousLinearMap.adjoint P w, a⟫_ℂ)) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 →
      ∫⁻ g : UJ ε, ENNReal.ofReal (colSq (um g⁻¹) (zi e) * ‖⟪ContinuousLinearMap.adjoint P w, π (um g) v⟫_ℂ‖ ^ 2) ∂(muG ε) ≤
        ENNReal.ofReal ((8 * ((n : ℝ) + 1) * B) ^ (8 * (n + 1))) *
          ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪ContinuousLinearMap.adjoint P w, π (um g) v⟫_ℂ‖ ^ 2) ∂(muG ε)

theorem momentHeA_of (hD : DecEx) (hC : Comat) (hW : WordBd) : MomentHeA := by
  intro n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ P w κ hI hw hξ hκ hm hconv hproj v hv hv1
  set ξ := ContinuousLinearMap.adjoint P w with hξd
  set z := zi e with hz
  obtain ⟨η, hηs, hη0, hproj⟩ := hproj
  set T : ℝ := 8 * ((n : ℝ) + 1) * B with hT
  have hU := hπ.2.2.1
  have hU' := hσ.2.2.1
  have hN2 : (2 : ℝ) ≤ n := by exact_mod_cast hP.two
  have hN3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  obtain ⟨a0, ha0⟩ := hP.neg
  have hB : 1 ≤ B := by
    have h1 := hP.gap z a0 (by rw [ha0, show ε z = true from hF.1]; simp)
    have h2 := (abs_sub _ _).trans (add_le_add (hP.bd z) (hP.bd a0))
    have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hTN : (n : ℝ) + 1 ≤ T := by rw [hT]; nlinarith
  have hT4 : 4 ≤ T := by rw [hT]; nlinarith
  obtain ⟨X⟩ := hD (n + 1) ε lam H π ⟨a0, ha0⟩ hP.le hP.hc hπ (by exact_mod_cast hP.gap)
  have hvs := (hW (n + 1) ε lam B H π (by have := hP.two; omega) hP.hc hπ hP.bd (fun a b hab => le_trans (by
    push_cast; have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
    linarith) (hP.gap a b hab)) v hv).1
  have hp1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := Finset.card_pos.2 ⟨z, by simpa using hF.1⟩
  have hq1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := Finset.card_pos.2 ⟨a0, by simpa using ha0⟩
  obtain ⟨c0, hc0, hfd⟩ := CompanionTheory.D.Upq.Coef.fdeg_gap (n + 1) ε
  have deg : ∀ (lam' : Fin (n + 1) → ℝ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (K →L[ℂ] K)), Formalism.QuantumDeterminants.IsHCParam lam' → IsDS ε lam' τ →
      Formalism.QuantumDeterminants.GapAtLeast ε lam' (120 * ((n : ℝ) + 1) ^ 3) → IsFdeg (muG ε) τ (c0 * Formalism.QuantumDeterminants.fdegHC lam') := by
    intro lam' K _ _ _ τ h1 h2 h3
    obtain ⟨d, hd⟩ := schur_UJ τ h2.2.1 h2.2.2.1 h2.2.2.2.1 h2.2.2.2.2.1
    have := h2.2.1
    obtain ⟨y, hy⟩ := exists_ne (0 : K)
    rw [← hfd lam' _ K τ y h1 h2 h3 (by push_cast; rfl) hp1 hq1 hy, Formalism.MainNotions.LowestKTypeMultiplicity.fdegOf_of_isFdeg hd hy]
    exact hd
  have h3 : (27 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by nlinarith [mul_self_nonneg ((n : ℝ) + 1)]
  have hd := deg lam H π hP.hc hπ fun a b hab => le_trans (by linarith) (hP.gap a b hab)
  set d := c0 * Formalism.QuantumDeterminants.fdegHC lam with hdd
  obtain ⟨i0, e0⟩ := Formalism.MainNotions.BridgeLemma.schur_abs hd v ξ
  rw [hv1, hξ, one_pow, mul_one] at e0
  haveI : ν.IsInvInvariant := by
    rw [Measure.isMulLeftInvariant_eq_smul ν (muG ε')]
    exact ⟨by rw [Measure.inv, Measure.map_smul]; exact congrArg _ (Measure.inv_eq_self (muG ε'))⟩
  have step : ∀ s ∈ X.S, ∀ l, Integrable (fun g : UJ ε => ‖⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ‖ ^ 2) (muG ε) ∧
      ∫ g : UJ ε, ‖⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ‖ ^ 2 ∂(muG ε) ≤ T ^ (6 * (n + 1)) * (1 / d) := by
    intro s hs l
    obtain ⟨hM, γ, hγ, hcor⟩ := hC n ε lam ε' mu B e H H' π σ ν hν hF hP hπ hσ X s hs
    have hUs := (X.ds s hs).2.2.2.1
    obtain ⟨b', hb1, hb2⟩ := idem_avg ν (fun h : UJ ε' => X.πs s (um (embU hF h)))
      (fun g h x => by
        rw [← u_mul hUs]
        exact congrArg (fun y => X.πs s y x) (emb_mul _ _))
      (fun g x y => u_adj hUs (embU hF g) x y) (fun g x => hUs.2.1 _ (umat_mem (embU hF g)) x)
      (fun x => (hUs.2.2 x).comp_continuous continuous_emb fun h => umat_mem (embU hF h))
      (fun h => conj ⟪w, σ (um h) w⟫_ℂ) (Complex.conjCLE.toContinuousLinearMap.integrable_comp hm)
      (fun g => by simp only [Complex.conj_conj]; rw [← u_adj hU', inner_conj_symm]) κ hconv (X.pr s (Pi.single z η))
    have main : ∀ x ∈ SmT ε π, κ * (⟪η, ξ⟫_ℂ * ⟪ξ, X.p s x z⟫_ℂ) = X.c s * ⟪b', X.pr s x⟫_ℂ := by
      intro x hx
      rw [← hproj, hb1, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun h => ?_)
      have e1 : π (emb e (um h)) (X.p s x z) = actT π (um (embU hF h)) (X.p s x) z := by
        unfold actT
        rw [← um_inv, Finset.sum_eq_single z (fun b _ hb => by
          rw [show um (embU hF h)⁻¹ b z = _ from emb_col _ b, if_neg hb, zero_smul]) (by simp),
          show um (embU hF h)⁻¹ z z = _ from emb_col _ z, if_pos rfl, one_smul]
        rfl
      have e2 := X.form s hs _ (smT_act hU (embU hF h) hx) _ (smT_single hηs z)
      rw [formT_single, show ε z = true from hF.1, if_pos rfl, one_mul, X.pr_act s hs _ _ hx, X.p_act s hs _ _ hx] at e2
      simp only
      rw [e1, e2]; ring
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have n1 : ‖X.c s‖ * ‖b'‖ ^ 2 = κ ^ 2 * ‖⟪η, ξ⟫_ℂ‖ ^ 2 * ‖γ‖ := by
      have h1 := main _ (smT_single hηs z)
      have ha : ∀ y, ⟪ξ, y⟫_ℂ = ⟪w, P y⟫_ℂ := fun y => ContinuousLinearMap.adjoint_inner_left P y w
      rw [ha, hcor P hI η hηs, inner_smul_right, ← ha] at h1
      have h2 : X.c s * ⟪b', b'⟫_ℂ = κ * (κ * (⟪η, ξ⟫_ℂ * (γ * ⟪ξ, η⟫_ℂ))) := by rw [hb2, h1]; ring
      have h4 := congrArg norm h2
      rw [norm_mul, inner_self_eq_norm_sq_to_K, norm_pow, norm_mul, norm_mul, norm_mul, norm_mul, norm_inner_symm ξ η,
        Complex.norm_real, Real.norm_of_nonneg hκ.le] at h4
      simp only [Complex.coe_algebraMap, Complex.norm_real, norm_norm] at h4
      rw [h4]; ring
    have n2 : ‖X.c s‖ * ‖X.pr s (Pi.single l v)‖ ^ 2 ≤ T ^ (4 * (n + 1)) := by
      have h1 := congrArg norm (X.form s hs _ (smT_single hvs l) _ (smT_single hvs l))
      rw [formT_single, norm_mul, norm_mul, inner_self_eq_norm_sq_to_K, norm_pow] at h1
      simp only [Complex.coe_algebraMap, Complex.norm_real, norm_norm] at h1
      rw [← h1, show ‖(if ε l then 1 else -1 : ℂ)‖ = 1 by split_ifs <;> simp, one_mul]
      refine (norm_inner_le_norm _ _).trans ?_
      have := hM v hv l l
      rw [hv1, mul_one] at this
      rwa [hv1, one_mul]
    have hds := deg _ _ (X.πs s) (X.ds s hs).1 (X.ds s hs).2 fun a b hab => by
      have h1 := hP.gap a b hab
      have h2 : |lam a - lam b| ≤ |(lam - Pi.single s 1 : Fin (n + 1) → ℝ) a - (lam - Pi.single s 1 : Fin (n + 1) → ℝ) b| + 1 := by
        rw [abs_le]
        have := le_abs_self ((lam - Pi.single s 1 : Fin (n + 1) → ℝ) a - (lam - Pi.single s 1 : Fin (n + 1) → ℝ) b)
        have := neg_abs_le ((lam - Pi.single s 1 : Fin (n + 1) → ℝ) a - (lam - Pi.single s 1 : Fin (n + 1) → ℝ) b)
        simp only [Pi.sub_apply, Pi.single_apply] at *
        split_ifs at * <;> constructor <;> linarith
      linarith
    obtain ⟨i1, e1⟩ := Formalism.MainNotions.BridgeLemma.schur_abs hds (X.pr s (Pi.single l v)) b'
    have hA : 0 < κ * ‖⟪η, ξ⟫_ℂ‖ := mul_pos hκ (norm_pos_iff.2 hη0)
    have hfun : (fun g : UJ ε => ‖⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ‖ ^ 2) =
        fun g => (‖X.c s‖ / (κ * ‖⟪η, ξ⟫_ℂ‖)) ^ 2 * ‖⟪b', X.πs s (umat g) (X.pr s (Pi.single l v))⟫_ℂ‖ ^ 2 := by
      funext g
      have h1 := congrArg norm (main _ (smT_act hU g (smT_single hvs l)))
      rw [X.pr_act s hs _ _ (smT_single hvs l), norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le] at h1
      rw [← mul_pow, div_mul_eq_mul_div, ← h1, ← mul_assoc, mul_div_cancel_left₀ _ hA.ne']
    rw [hfun]
    refine ⟨i1.const_mul _, ?_⟩
    rw [integral_const_mul, e1]
    have hr : 1 / (c0 * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1)) ≤ T ^ (n + 1) * (1 / d) := by
      rw [mul_one_div, div_le_div_iff₀ hds.1 hd.1, one_mul, hdd, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ((fdeg_shift s (X.ds s hs).1).trans (mul_le_mul_of_nonneg_right ?_
        ((mul_pos_iff_of_pos_left hc0).1 hds.1).le)) hc0.le
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith) _
    calc _ = ‖γ‖ * (‖X.c s‖ * ‖X.pr s (Pi.single l v)‖ ^ 2) * (1 / (c0 * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1))) := by
          have : ‖γ‖ = ‖X.c s‖ * ‖b'‖ ^ 2 / (κ * ‖⟪η, ξ⟫_ℂ‖) ^ 2 := by rw [n1]; field_simp
          rw [this]; ring
      _ ≤ T ^ (n + 1) * T ^ (4 * (n + 1)) * (T ^ (n + 1) * (1 / d)) :=
          mul_le_mul (mul_le_mul hγ n2 (by positivity) (by positivity)) hr (one_div_pos.2 hds.1).le (by positivity)
      _ = _ := by ring
  have hcard : (X.S.card : ℝ) ≤ T := le_trans (by exact_mod_cast (X.S.card_le_univ.trans (by simp))) hTN
  have pt : ∀ g : UJ ε, colSq (um g⁻¹) z * ‖⟪ξ, π (um g) v⟫_ℂ‖ ^ 2 ≤
      T * ∑ l, ∑ s ∈ X.S, ‖⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ‖ ^ 2 := by
    intro g
    rw [colSq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    have e1 : um g⁻¹ l z * ⟪ξ, π (um g) v⟫_ℂ = ∑ s ∈ X.S, ⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ := by
      rw [← inner_sum, ← Finset.sum_apply, X.sum _ (smT_act hU g (smT_single hvs l)), actT_single, inner_smul_right, um_inv]
    rw [← mul_pow, ← norm_mul, e1]
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans (sq_sum_le_card_mul_sum_sq.trans ?_)
    exact mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => by positivity)
  have iS : Integrable (fun g : UJ ε => T * ∑ l, ∑ s ∈ X.S, ‖⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ‖ ^ 2) (muG ε) :=
    (integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun s hs => (step s hs l).1).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal i0 (.of_forall fun _ => by positivity), e0, ← ENNReal.ofReal_mul (by positivity)]
  refine (lintegral_mono fun g => ENNReal.ofReal_le_ofReal (pt g)).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal iS (.of_forall fun _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_const_mul, integral_finsetSum _ fun l _ => integrable_finsetSum _ fun s hs => (step s hs l).1]
  have hd0 : 0 ≤ T ^ (6 * (n + 1)) * (1 / d) := mul_nonneg (by positivity) (one_div_pos.2 hd.1).le
  have hl : ∀ l, ∫ g : UJ ε, ∑ s ∈ X.S, ‖⟪ξ, X.p s (actT π (um g) (Pi.single l v)) z⟫_ℂ‖ ^ 2 ∂(muG ε) ≤
      T * (T ^ (6 * (n + 1)) * (1 / d)) := fun l => by
    rw [integral_finsetSum _ fun s hs => (step s hs l).1]
    refine (Finset.sum_le_card_nsmul _ _ _ fun s hs => (step s hs l).2).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hd0
  calc _ ≤ T * (T * (T * (T ^ (6 * (n + 1)) * (1 / d)))) := by
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_card_nsmul _ _ _ fun l _ => hl l).trans ?_) (by linarith)
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using hTN) (mul_nonneg (by linarith) hd0)
    _ = T ^ (6 * (n + 1) + 3) * (1 / d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by have := hP.two; omega)) (one_div_pos.2 hd.1).le

theorem moment_higher_estimate_holds : MomentHeA := momentHeA_of DecB.unitary_decomposition_exists Com.comatrix_word_bound CompanionTheory.Lime.T3.kFiniteWordBound_indefUnitary

end PositivityTheory.UnitaryDecomposition

namespace PositivityTheory.RgHe.A.Pf

theorem momentP : PositivityTheory.RgHe.A.MomentP := fun n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ =>
  PositivityTheory.UnitaryDecomposition.moment_higher_estimate_holds n ε lam ε' mu B e H H' π σ ν hν hF
    ⟨hP.two, hP.neg, hP.le, hP.hc, hP.hc', hP.bd, hP.bd', hP.gap, hP.gap'⟩ hπ hσ

end PositivityTheory.RgHe.A.Pf
