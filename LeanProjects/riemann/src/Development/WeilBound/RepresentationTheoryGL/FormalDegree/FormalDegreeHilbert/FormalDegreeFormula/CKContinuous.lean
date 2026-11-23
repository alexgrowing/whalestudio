import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.ModelFunctionsMultiply

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : Continuous (cK T) :=
  (continuous_const.inner ((CompactHaarProbability.cont_op T).clm_apply continuous_const)).norm

theorem op_norm {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (v : T.V) : ‖T.op k v‖ = ‖v‖ := by
  have h : T.op k⁻¹ * T.op k = 1 := CompactHaarProbability.op_inv_mul T k
  have hs : star (T.op k) * T.op k = 1 := Unitary.star_mul_self_of_mem (T.τ k).prop
  have h2 : ‖T.op k v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    congr 1
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hs, ContinuousLinearMap.one_apply]
  have := h
  nlinarith [norm_nonneg (T.op k v), norm_nonneg v, sq_nonneg (‖T.op k v‖ - ‖v‖), sq_nonneg (‖T.op k v‖ + ‖v‖)]

theorem cK_le_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : cK T k ≤ 1 := by
  unfold cK
  calc ‖⟪T.w, T.op k T.w⟫_ℂ‖ ≤ ‖T.w‖ * ‖T.op k T.w‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [op_norm, T.w_norm, one_mul]

abbrev CPair (ε : Fin n → Bool) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ε p.1 = ε p.2}

theorem prod_cpair (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), f a b = ∏ p : CPair ε, f p.1.1 p.1.2 := by
  have e1 : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b), f a b =
      ∏ x ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = ε x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    simp_rw [Finset.prod_filter]
  rw [e1, ← Finset.prod_subtype (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 = ε x.2))
    (fun x => by simp) (fun x : Fin n × Fin n => f x.1 x.2)]

theorem kNull_of (hW : MomW) (hP : CoefPow) : KNull := by
  intro n ε lam hl T TD
  classical
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  set F : ℝ := (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) * ∏ i ∈ range (qOf ε), (i.factorial : ℝ) with hF
  have hFpos : 0 < F := by positivity
  let α : CPair ε → ℝ := fun p => lam p.1.1 - lam p.1.2 + (nab ε p.1.1 p.1.2 : ℝ)
  let β : CPair ε → ℝ := fun p => ((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)
  have hα : ∀ p, 0 < α p := fun p => by
    have := hl.1 p.2.1
    have : (0 : ℝ) ≤ nab ε p.1.1 p.1.2 := Nat.cast_nonneg _
    simp only [α]; linarith
  have hβ : ∀ p, 0 ≤ β p := fun p => by
    have : ((p.1.1 : ℕ) : ℝ) < ((p.1.2 : ℕ) : ℝ) := by exact_mod_cast p.2.1
    simp only [β]; linarith

  have hmom : ∀ t : ℕ, ∫⁻ k, ENNReal.ofReal (cK T k ^ 2) * ENNReal.ofReal ((cK TD k ^ 2) ^ t) ∂(dk ε) =
      ENNReal.ofReal (F / ∏ p, (α p + t * β p)) := by
    intro t
    obtain ⟨Tt⟩ := kType_exists ε (lamT lam t) (isHCParam_lamT hl t)
    have e : ∀ k, ENNReal.ofReal (cK T k ^ 2) * ENNReal.ofReal ((cK TD k ^ 2) ^ t) = ENNReal.ofReal (cK Tt k ^ 2) := by
      intro k
      rw [← ENNReal.ofReal_mul (sq_nonneg _), hP n ε lam hl T TD t Tt k]
      ring_nf
    simp_rw [e]
    have hint : Integrable (fun k => cK Tt k ^ 2) (dk ε) :=
      ((cK_continuous Tt).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun k => sq_nonneg _)]
    congr 1
    have hs := kschur_coef Tt Tt.w Tt.w
    rw [Tt.w_norm] at hs
    have h7 := lemma7 Tt
    have hd : (0 : ℝ) < Module.finrank ℂ Tt.V := by
      have : Nontrivial Tt.V := ⟨⟨Tt.w, 0, fun h => by have := Tt.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
      exact_mod_cast Module.finrank_pos
    have hI : ∫ k, cK Tt k ^ 2 ∂(dk ε) = (Module.finrank ℂ Tt.V : ℝ)⁻¹ := by
      unfold cK
      field_simp
      linarith
    rw [hI, h7, prod_cpair ε (fun a b => lamT lam t a - lamT lam t b + (nab ε a b : ℝ))]
    have e2 : ∀ p : CPair ε, lamT lam t p.1.1 - lamT lam t p.1.2 + (nab ε p.1.1 p.1.2 : ℝ) = α p + t * β p := by
      intro p
      simp only [lamT_apply, Dvec, α, β]
      ring
    simp_rw [e2]
    rw [inv_div]
  have h0 := hmom 0
  simp only [pow_zero, ENNReal.ofReal_one, mul_one, Nat.cast_zero, zero_mul, add_zero] at h0
  have hpos := hW (KG ε) (dk ε) (fun k => ENNReal.ofReal (cK T k ^ 2)) (fun k => cK TD k ^ 2) (CPair ε) α β F 0
    ((cK_continuous T).pow 2).measurable.ennreal_ofReal ((cK_continuous TD).pow 2).measurable
    (fun k => ⟨sq_nonneg _, by have h1 := cK_le_one TD k; have h2 : 0 ≤ cK TD k := norm_nonneg _; nlinarith⟩) hα hβ hFpos.le
    (fun t _ => hmom t)
  set s : Set (KG ε) := {k | 0 < cK TD k ^ 2} with hs
  have hsm : MeasurableSet s := measurableSet_lt measurable_const ((cK_continuous TD).pow 2).measurable
  have hsum := lintegral_add_compl (fun k => ENNReal.ofReal (cK T k ^ 2)) (μ := dk ε) hsm
  rw [hpos, h0] at hsum
  have hz : ∫⁻ k in sᶜ, ENNReal.ofReal (cK T k ^ 2) ∂(dk ε) = 0 := by
    have hne : ENNReal.ofReal (F / ∏ p, α p) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc _ = ENNReal.ofReal (F / ∏ p, α p) + (∫⁻ k in sᶜ, ENNReal.ofReal (cK T k ^ 2) ∂(dk ε)) -
          ENNReal.ofReal (F / ∏ p, α p) := by rw [ENNReal.add_sub_cancel_left hne]
      _ = 0 := by rw [hsum, tsub_self]
  have hmeas : Measurable fun k => ENNReal.ofReal (cK T k ^ 2) := by
    exact ((cK_continuous T).pow 2).measurable.ennreal_ofReal
  replace hz := (lintegral_eq_zero_iff hmeas).1 hz
  rw [Filter.EventuallyEq, ae_restrict_iff' hsm.compl] at hz
  filter_upwards [hz] with k hk h0k
  have hk' := hk (by simp [hs, h0k])
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hk'
  nlinarith [sq_nonneg (cK T k), norm_nonneg (⟪T.w, T.op k T.w⟫_ℂ)]

end PositivityTheory.RgFd
