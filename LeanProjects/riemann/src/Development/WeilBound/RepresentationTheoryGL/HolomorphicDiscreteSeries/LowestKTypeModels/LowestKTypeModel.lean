import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.ApplyNeZero
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.KFiniteWordBoundIndefUnitary

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.LowestKTypeUnitIntegral

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.MainNotions.BridgeCSchur CompanionTheory.D.Upq.Sm

theorem lowestKTypeModel : Seed := by
  intro n ε lam ε' mu e hG H H' _ _ _ _ _ _ π σ ν hν hπ hσ ⟨j, hj0, hj⟩ κ hK w hw hw1
  haveI := hν
  haveI := inv_inv_of_haar ν
  have hm := coef_int hG.two hG.hc' hσ hG.gap' ν hw hw1
  refine ⟨hm, ?_⟩
  have hρ := uRep_emb hG.fits hπ.2.2.1
  have hs := uRep_self hσ.2.2.1
  have hS : ∀ v w v' w' : H', ∫ g : UJ ε', ⟪w, σ (um g) v⟫_ℂ * conj ⟪w', σ (um g) v'⟫_ℂ ∂ν = κ * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ) :=
    fun v w v' w' => (hK.2 v w v' w').2
  have hw0 : w ≠ 0 := norm_ne_zero_iff.1 (by rw [hw1]; exact one_ne_zero)
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  set φ : UJ ε' → ℂ := fun h => conj ⟪w, σ (um h) w⟫_ℂ with hφd
  have hφ : Integrable φ ν := Complex.conjCLE.toContinuousLinearMap.integrable_comp hm
  set ρ : UJ ε' → (H →L[ℂ] H) := fun h => π (emb e (um h)) with hρd

  set b0 := j w with hb0
  have hint : ∀ b a : H, Integrable (fun h => φ h * ⟪b, ρ h a⟫_ℂ) ν := fun b a =>
    hφ.mul_bdd (c := ‖b‖ * ‖a‖) (continuous_const.inner (hρ.cont a)).aestronglyMeasurable
      (.of_forall fun h => (norm_inner_le_norm _ _).trans (by rw [hρ.nrm]))
  let L0 : H →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ h, φ h * ⟪b0, ρ h a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint _ a) (hint _ a')]
        simp only [map_add, inner_add_right, mul_add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        simp only [map_smul, inner_smul_right]
        congr 1; funext h; ring }
  let Lc : H →L[ℂ] ℂ := L0.mkContinuous ((∫ h, ‖φ h‖ ∂ν) * ‖b0‖) fun a => by
    show ‖∫ h, φ h * ⟪b0, ρ h a⟫_ℂ ∂ν‖ ≤ _
    refine (norm_integral_le_of_norm_le (hφ.norm.mul_const (‖b0‖ * ‖a‖)) (.of_forall fun h => ?_)).trans
      (le_of_eq ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans (by rw [hρ.nrm])) (norm_nonneg _)
    · rw [integral_mul_const]; ring
  have hLc : ∀ a, Lc a = ∫ h, φ h * ⟪b0, ρ h a⟫_ℂ ∂ν := fun a => rfl

  have hjw : b0 ≠ 0 := apply_ne_zero hσ.2.2.2.1 hj0 hj hw0
  have hLb : Lc b0 ≠ 0 := by
    rw [hLc]
    have e1 : ∀ h : UJ ε', φ h * ⟪b0, ρ h b0⟫_ℂ =
        ⟪ContinuousLinearMap.adjoint j b0, σ (um h) w⟫_ℂ * conj ⟪w, σ (um h) w⟫_ℂ := fun h => by
      rw [ContinuousLinearMap.adjoint_inner_left, hj, mul_comm]
    simp only [e1, hS, hww, one_mul]
    rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    have : (0 : ℝ) < ‖b0‖ := norm_pos_iff.2 hjw
    have hκ := hK.1
    exact mul_ne_zero (by exact_mod_cast hκ.ne') (pow_ne_zero _ (by simp [hjw]))

  obtain ⟨v0, hv0, hv01⟩ := exists_lowK_unit hπ
  have hv0n : v0 ≠ 0 := norm_ne_zero_iff.1 (by rw [hv01]; exact one_ne_zero)
  have hv0s := (CompanionTheory.Lime.T3.kFiniteWordBound_indefUnitary (n + 1) ε lam (∑ a, |lam a|) H π (by have := hG.two; omega) hG.hc hπ
    (fun a => Finset.single_le_sum (f := fun a => |lam a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
    (fun a b hab => le_trans (by push_cast; have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
                                 linarith) (hG.gap a b hab)) v0 hv0).1
  obtain ⟨g1, hg1⟩ : ∃ g : UJ ε, Lc (π (um g) v0) ≠ 0 := by
    by_contra hno
    push_neg at hno
    set D := Submodule.span ℂ (Set.range fun g : UJ ε => π (um g) v0) with hDd
    have hD : ∀ g : UJ ε, ∀ y ∈ D, π (um g) y ∈ D := fun g y hy => by
      refine Submodule.span_induction (p := fun y _ => π (um g) y ∈ D) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨g', rfl⟩
        exact Submodule.subset_span ⟨g * g', u_mul hπ.2.2.1 g g' v0⟩
      · simp
      · intro x y _ _ hx hy; rw [map_add]; exact D.add_mem hx hy
      · intro c x _ hx; rw [map_smul]; exact D.smul_mem c hx
    have hv0D : v0 ∈ D := Submodule.subset_span ⟨1, by
      show π (um (1 : UJ ε)) v0 = v0
      rw [show um (1 : UJ ε) = 1 from rfl, hπ.2.2.1.1.1]; rfl⟩
    have hcl : D.topologicalClosure = ⊤ := by
      rcases irr_of hπ.2.2.2.1 D.topologicalClosure D.isClosed_topologicalClosure
          (fun g v hv => map_mem_closure (π (umat g)).continuous hv (hD g)) with h | h
      · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ D.le_topologicalClosure hv0D)) hv0n
      · exact h
    have hle : D.topologicalClosure ≤ LinearMap.ker (Lc : H →ₗ[ℂ] ℂ) :=
      Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hno g))
        Lc.isClosed_ker
    exact hLb (hle (hcl ▸ Submodule.mem_top))
  set η := π (um g1) v0 with hηd
  have hηs : η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π := IsSm.apply (repOn hπ.2.2.1) hv0s g1.2

  obtain ⟨j', hj'1, hj'2⟩ := exists_intertwiner ν hρ hs (irr_of hσ.2.2.2.1) κ hS w hw0 hm η
  set ξ0 := j' w with hξ0d
  have hξ0 : ξ0 ≠ 0 := fun h0 => hg1 (by rw [hLc, ← hj'2 b0, h0, inner_zero_right])

  have hsym : ∀ g, φ g⁻¹ = conj (φ g) := fun g => by
    show conj _ = conj (conj _)
    rw [← u_adj hσ.2.2.1 g w w, Complex.conj_conj, inner_conj_symm]
  have hconv : ∀ x, ∫ h, φ h * φ (h⁻¹ * x) ∂ν = (κ : ℂ) * φ x := fun x => by
    have := (hK.2 w (σ (um x) w) w w).2
    rw [inner_self_eq_norm_sq_to_K, hw1] at this
    show ∫ h, conj ⟪w, σ (um h) w⟫_ℂ * conj ⟪w, σ (um (h⁻¹ * x)) w⟫_ℂ ∂ν = (κ : ℂ) * conj ⟪w, σ (um x) w⟫_ℂ
    rw [inner_conj_symm (σ (um x) w), show (κ : ℂ) * ⟪σ (um x) w, w⟫_ℂ = κ * ((((1 : ℝ) : ℂ)) ^ 2 * ⟪σ (um x) w, w⟫_ℂ) by simp]
    refine Eq.trans (integral_congr_ae (.of_forall fun h => ?_)) this
    have a1 := hs.adj h w (σ (um x) w)
    simp only at a1 ⊢
    rw [u_mul hσ.2.2.1, ← a1, inner_conj_symm (σ (um x) w), mul_comm]
  obtain ⟨b', hb1, hb2⟩ := idem_avg ν ρ hρ.mul hρ.adj hρ.nrm hρ.cont φ hφ hsym κ hconv η
  have h7 : ∀ a, ⟪ξ0, a⟫_ℂ = ∫ h, φ h * ⟪η, ρ h a⟫_ℂ ∂ν := fun a => by
    rw [← inner_conj_symm, hj'2 a, ← integral_conj, ← integral_inv_eq_self (fun h => φ h * ⟪η, ρ h a⟫_ℂ) ν]
    refine integral_congr_ae (.of_forall fun h => ?_)
    simp only [map_mul, hsym, inner_conj_symm, hρ.adj, hφd]
    rw [u_adj hσ.2.2.1, inv_inv]
  have hbξ : b' = ξ0 := ext_inner_right ℂ fun a => by rw [hb1, h7]
  rw [hbξ] at hb2

  obtain ⟨c, hc⟩ := isom_of hσ.2.2.1 hσ.2.2.2.1 hρ j' hj'1
  set r := ‖ξ0‖ with hrd
  have hr : 0 < r := norm_pos_iff.2 hξ0
  have hcr : c = ((r ^ 2 : ℝ) : ℂ) := by
    have := hc w
    rw [hww, mul_one, ← hξ0d, inner_self_eq_norm_sq_to_K] at this
    rw [← this]; push_cast; rfl
  have hnj : ∀ x, ‖j' x‖ = r * ‖x‖ := fun x => by
    have h1 := hc x
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hcr] at h1
    have h3 : ((‖j' x‖ ^ 2 : ℝ) : ℂ) = ((r ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) := by push_cast at h1 ⊢; exact h1
    have h2 : ‖j' x‖ ^ 2 = (r * ‖x‖) ^ 2 := by rw [mul_pow]; exact Complex.ofReal_injective h3
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hK.1.ne'
  have hq : ⟪ξ0, η⟫_ℂ = ((r ^ 2 / κ : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K] at hb2
    push_cast
    rw [eq_div_iff hκ0]
    linear_combination -hb2
  have hq' : ⟪η, ξ0⟫_ℂ = ((r ^ 2 / κ : ℝ) : ℂ) := by rw [← inner_conj_symm, hq, Complex.conj_ofReal]
  refine ⟨((r⁻¹ : ℝ) : ℂ) • j', η, fun x => ?_, fun h x => ?_, hηs, ?_, fun a => ?_⟩
  · rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hr).le, hnj,
      ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [hj'1]
  · rw [ContinuousLinearMap.smul_apply, ← hξ0d, inner_smul_right, hq']
    have : (0 : ℝ) < r ^ 2 / κ := div_pos (by positivity) hK.1
    exact mul_ne_zero (by exact_mod_cast (inv_pos.2 hr).ne') (by exact_mod_cast this.ne')
  · rw [ContinuousLinearMap.smul_apply, ← hξ0d, inner_smul_right, inner_smul_left, hq', Complex.conj_ofReal, ← h7]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp

end PositivityTheory.RgHe.LowestKTypeUnitIntegral
