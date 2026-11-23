import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB.D1
open GroundTheory.Automorphic.Reduction
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

theorem admissible_le_holds : AdmLe := by
  intro n t₀ x ht h i j hij
  have key : ∀ k : ℕ, ∀ hk : i.1 + k < n, x ⟨i.1 + k, hk⟩ ≤ x i + k * t₀ := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have h1 := h (i.1 + k + 1)
      unfold An.sr at h1
      rw [dif_pos ⟨by omega, by omega⟩] at h1
      have h2 := ih (by omega)
      have e : (⟨i.1 + k + 1 - 1, by omega⟩ : Fin n) = ⟨i.1 + k, by omega⟩ := Fin.ext (by simp)
      rw [e] at h1
      push_cast
      have e2 : x ⟨i.1 + (k + 1), hk⟩ = x ⟨i.1 + k + 1, by omega⟩ := rfl
      linarith
  have hij' : i.1 ≤ j.1 := hij
  have h3 := key (j.1 - i.1) (by omega)
  have e : (⟨i.1 + (j.1 - i.1), by omega⟩ : Fin n) = j := Fin.ext (by simp only; omega)
  rw [e] at h3
  have h4 : ((j.1 - i.1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j.1 - i.1 ≤ n)
  nlinarith

theorem cover_holds : Cover := by
  intro E _ _ _ n
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) n
  refine ⟨ω, max 0 (-Real.log t), ⟨hω, hωB⟩, le_max_left _ _, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, hg⟩ := hsieg g
  have ha : diagUnits n (fun i => posIdele (K := E) (r i) (hr i)) = An.tor E fun i => Real.log (r i) := by
    unfold An.tor
    congr 1
    funext i
    exact JSqIntGlue.posIdele_congr (Real.exp_log (hr i)).symm _ _
  refine ⟨γ, b, hb, fun i => Real.log (r i), fun r' => ?_, k, hk, ha ▸ hg⟩
  unfold An.sr
  split_ifs with h
  · have h1 := hratio ⟨r' - 1, by omega⟩ ⟨r', h.2⟩ (by simp only; omega)
    have h2 := Real.log_le_log (mul_pos ht (hr _)) h1
    rw [Real.log_mul ht.ne' (hr _).ne'] at h2
    have := le_max_right 0 (-Real.log t)
    linarith
  · have := le_max_left 0 (-Real.log t); linarith

theorem cellCover_of (h1 : Cover) (h2 : ConjCpt) : CellCover := by
  intro E _ _ _ n
  obtain ⟨ω, t₀, hω, ht, hc⟩ := h1 E n
  obtain ⟨ω', hω', hj⟩ := h2 E n ω t₀ hω ht
  refine ⟨(fun p : (Fin n → ℝ) × GA E n × GA E n => An.tor E p.1 * p.2.1 * p.2.2) ''
    (Metric.closedBall 0 1 ×ˢ ω' ×ˢ (maxCompact (K := E) (n := n) : Set _)), ?_, fun g => ?_⟩
  · exact ((isCompact_closedBall _ _).prod (hω'.prod isCompact_maxCompact)).image
      (((JSqIntGlue.continuous_tor.comp continuous_fst).mul continuous_snd.fst).mul continuous_snd.snd)
  · obtain ⟨γ, b, hb, x, hx, k, hk, e⟩ := hc g
    refine ⟨γ, fun i => ⌊x i⌋, _, ⟨(fun i => Int.fract (x i), _, k), ⟨?_, hj b hb x hx, hk⟩, rfl⟩, ?_⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    · have e2 : (An.tor E x : GA E n) = An.tor E (fun i => (⌊x i⌋ : ℝ)) * An.tor E (fun i => Int.fract (x i)) := by
        rw [← JSqIntGlue.tor_add]
        congr 1
        funext i
        exact (Int.floor_add_fract _).symm
      rw [e]
      simp only [← mul_assoc]
      rw [← e2, mul_inv_cancel, one_mul]

theorem discrete_range (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) :
    DiscreteTopology (ratGL E n).range :=
  DiscreteTopology.of_continuous_injective (β := latticeGL E n) (f := Subgroup.inclusion le_sup_left)
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

theorem domEx_holds : DomEx := by
  intro E _ _ _ n _ _ μ
  have := discrete_range E n
  exact ⟨_, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩

theorem ratProper_holds : RatProper := by
  intro E _ _ _ n
  have hi : Function.Injective (ratGL E n) := fun a b h => Units.ext <| Matrix.ext fun i j =>
    AdeleRing.algebraMap_injective (𝓞 E) E (congrArg (fun g : GA E n => g.val i j) h)
  have := discrete_range E n
  refine ⟨hi, (MonoidHom.ofInjective hi).injective.countable, fun C hC => ?_⟩
  exact (GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := (ratGL E n).range) hC).preimage
    (f := MonoidHom.ofInjective hi) (MonoidHom.ofInjective hi).injective.injOn

theorem img_top {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) : img g ⊤ = ⊤ := by
  refine eq_top_iff.2 fun v _ => ⟨(g⁻¹).val *ᵥ v, trivial, ?_⟩
  simp [Matrix.mulVec_mulVec]

theorem img_img_inv {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g (img g⁻¹ W) = W := by
  unfold img
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one, Submodule.map_id]

theorem finrank_img {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (img g W) = Module.finrank K W := by
  refine le_antisymm (Submodule.finrank_map_le _ _) ?_
  conv_lhs => rw [← img_img_inv g⁻¹ W, inv_inv]
  exact Submodule.finrank_map_le _ _

theorem cutBox_of (h : DegCell) : CutBox := by
  intro E _ _ _ n Ω₀ hΩ
  obtain ⟨C, hC⟩ := h E n Ω₀ hΩ
  refine ⟨(n + 1) * (1 + |C|), by positivity, fun x o ho σ hσ h1 h2 => ?_⟩
  obtain ⟨a1, a2⟩ := hC x o ho
  have hd : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hc := le_abs_self C
  have hc0 := abs_nonneg C
  have b1 : ∀ i, x i ≤ σ + |C| := fun i => by
    have := h1 _ (finrank_span_singleton (v := (Pi.single i 1 : Fin n → E)) (by simp))
    have := (abs_le.1 (a1 i)).1
    by_contra hn
    nlinarith
  have b2 : -(σ + |C|) ≤ ∑ i, x i := by
    have := (abs_le.1 a2).2
    by_contra hn
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have b3 : ∑ j, (σ + |C| - x j) = n * (σ + |C|) - ∑ j, x j := by simp [Finset.sum_sub_distrib, mul_add]
  have b4 := Finset.single_le_sum (f := fun j => σ + |C| - x j) (fun j _ => sub_nonneg.2 (b1 j)) (Finset.mem_univ i)
  have b5 : (n + 1) * (σ + |C|) ≤ (n + 1) * (1 + |C|) * (1 + σ) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [b1 i]

theorem cutRed_of (h1 : DegRat) (h2 : CellCover) (h3 : CutBox) (h4 : RedBasic) (h5 : RedCell) : CutRed := by
  intro E _ _ _ n
  obtain ⟨Ω₀, hΩ, hc⟩ := h2 E n
  obtain ⟨C, hC0, hC⟩ := h3 E n Ω₀ hΩ
  obtain ⟨C', hC0', hC'⟩ := h5 E n Ω₀ hΩ
  refine ⟨C' * (1 + C * (2 * n + 1)), by positivity, fun τ hτ g hg => ?_⟩
  obtain ⟨γ, m, o, ho, e⟩ := hc g
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have a := hC (fun i => (m i : ℝ)) o ho ((2 * n + 1) * τ) (by positivity) (fun W hW => by
    rw [← e, ← img_img_inv γ W, h1]
    refine (hg.1 _).trans ?_
    rw [finrank_img, hW, prof]
    push_cast
    nlinarith) (by
    rw [← e, ← img_top γ, h1]
    nlinarith [hg.2])
  rw [← (h4 E n).1 γ g, e]
  refine (hC' _ o ho).2.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0'
  have : 0 ≤ C * n := by positivity
  nlinarith

theorem redBasic_of (h1 : RatProper) (h2 : SizeCont) : RedBasic := by
  intro E _ _ _ n
  have h0 : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)
  have h0' : ∀ g : GA E n, 0 ≤ logSize g := fun g => add_nonneg (h0 _) (h0 _)
  refine ⟨fun γ g => ?_, fun g => ⟨le_ciInf fun _ => h0' _, ?_⟩, ?_⟩
  · unfold red
    rw [← (Equiv.mulRight γ).iInf_comp (g := fun δ => logSize (ratGL E n δ * g))]
    simp [mul_assoc]
  · refine (ciInf_le ⟨0, ?_⟩ 1).trans (by simp)
    rintro _ ⟨γ, rfl⟩
    exact h0' _
  · have := (h1 E n).2.1
    exact Measurable.iInf fun γ => ((h2 E n).comp (continuous_const.mul continuous_id)).measurable

theorem thetaBasic_holds : ThetaBasic := by
  intro E _ _ _ n
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun g => ?_, fun γ => ?_⟩
  · exact (Units.continuous_coe_inv.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · exact (Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · exact Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.conjAd_conjAd _)
  · exact Units.ext (Matrix.ext fun i j => conjAd_algebraMap _)

end PositivityTheory.Rg.BcB.E1

end
