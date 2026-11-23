import Mathlib
open MeasureTheory

namespace GlobalTheory

noncomputable section

abbrev SchwartzJetSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (N : ℕ) : Type :=
  (n : Fin (N + 1)) → BoundedContinuousFunction V (ContinuousMultilinearMap ℝ (fun _ : Fin (n : ℕ) => V) ℂ)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

example (N : ℕ) : CompleteSpace (SchwartzJetSpace V N) := inferInstance
example (N : ℕ) : NormedSpace ℂ (SchwartzJetSpace V N) := inferInstance

lemma schwartzJet_norm_bound (K N : ℕ) (f : SchwartzMap V ℂ) (n : Fin (N + 1)) (x : V) :
    ‖((1 + ‖x‖) ^ K : ℝ) • iteratedFDeriv ℝ (n : ℕ) f x‖ ≤
      2 ^ K * (Finset.Iic (K, N)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact SchwartzMap.one_add_le_sup_seminorm_apply (m := (K, N)) le_rfl (Nat.lt_succ_iff.1 n.2) f x

def schwartzJetFun (K N : ℕ) (f : SchwartzMap V ℂ) : SchwartzJetSpace V N := fun n =>
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ((1 + ‖x‖) ^ K : ℝ) • iteratedFDeriv ℝ (n : ℕ) f x)
    (((continuous_const.add continuous_norm).pow K).smul
      ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    _ (schwartzJet_norm_bound K N f n)

lemma schwartzJetFun_apply (K N : ℕ) (f : SchwartzMap V ℂ) (n : Fin (N + 1)) (x : V) :
    schwartzJetFun K N f n x = ((1 + ‖x‖) ^ K : ℝ) • iteratedFDeriv ℝ (n : ℕ) f x := rfl

def schwartzJet (K N : ℕ) : SchwartzMap V ℂ →ₗ[ℂ] SchwartzJetSpace V N where
  toFun := schwartzJetFun K N
  map_add' f g := by
    funext n; ext x : 1
    simp only [schwartzJetFun_apply, Pi.add_apply, BoundedContinuousFunction.coe_add]
    have e : (⇑(f + g) : V → ℂ) = ⇑f + ⇑g := rfl
    rw [e, iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add]
  map_smul' c f := by
    funext n; ext x : 1
    simp only [schwartzJetFun_apply, Pi.smul_apply, BoundedContinuousFunction.coe_smul, RingHom.id_apply]
    have e : (⇑(c • f) : V → ℂ) = c • ⇑f := rfl
    rw [e, iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_comm]

lemma schwartzJet_apply (K N : ℕ) (f : SchwartzMap V ℂ) (n : Fin (N + 1)) (x : V) :
    schwartzJet K N f n x = ((1 + ‖x‖) ^ K : ℝ) • iteratedFDeriv ℝ (n : ℕ) f x := rfl

lemma norm_schwartzJet_le (K N : ℕ) (f : SchwartzMap V ℂ) :
    ‖schwartzJet K N f‖ ≤ 2 ^ K * (Finset.Iic (K, N)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun n => ?_
  exact (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => schwartzJet_norm_bound K N f n x

lemma sup_seminorm_le_norm_schwartzJet (K N : ℕ) (f : SchwartzMap V ℂ) :
    (Finset.Iic (K, N)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f ≤ ‖schwartzJet K N f‖ := by
  refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun m hm => ?_
  rw [Finset.mem_Iic] at hm
  refine SchwartzMap.seminorm_le_bound ℂ m.1 m.2 f (norm_nonneg _) fun x => ?_
  have hn : m.2 < N + 1 := Nat.lt_succ_of_le hm.2
  calc ‖x‖ ^ m.1 * ‖iteratedFDeriv ℝ m.2 f x‖ ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ m.2 f x‖ := by
        gcongr
        calc ‖x‖ ^ m.1 ≤ (1 + ‖x‖) ^ m.1 := by gcongr; linarith
          _ ≤ (1 + ‖x‖) ^ K := pow_le_pow_right₀ (by linarith [norm_nonneg x]) hm.1
    _ = ‖schwartzJet K N f ⟨m.2, hn⟩ x‖ := by
        rw [schwartzJet_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ ‖schwartzJet K N f ⟨m.2, hn⟩‖ := BoundedContinuousFunction.norm_coe_le_norm _ x
    _ ≤ ‖schwartzJet K N f‖ := norm_le_pi_norm _ _

lemma continuous_schwartzJet (K N : ℕ) : Continuous (schwartzJet (V := V) K N) := by
  refine (schwartz_withSeminorms ℂ V ℂ).continuous_normedSpace_rng _ (schwartzJet K N)
    ⟨Finset.Iic (K, N), 2 ^ K, fun f => ?_⟩
  have h := norm_schwartzJet_le K N f
  refine h.trans (le_of_eq ?_)
  rw [Seminorm.smul_apply, NNReal.smul_def]
  simp only [NNReal.coe_pow, NNReal.coe_ofNat]
  rfl

lemma schwartzJet_injective (K N : ℕ) : Function.Injective (schwartzJet (V := V) K N) := by
  intro f g hfg
  ext x
  have h := congrArg (fun y : SchwartzJetSpace V N => y 0 x) hfg
  simp only [schwartzJet_apply] at h
  have h2 : iteratedFDeriv ℝ 0 f x = iteratedFDeriv ℝ 0 g x :=
    smul_right_injective _ (by positivity : ((1 + ‖x‖) ^ K : ℝ) ≠ 0) h
  simpa using congrArg (fun A => A (fun _ => 0)) h2

lemma exists_jet_factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) :
    ∃ K N : ℕ, ∃ L : SchwartzJetSpace V N →L[ℂ] ℂ, ∀ f, T f = L (schwartzJet K N f) := by
  set q : Seminorm ℂ (SchwartzMap V ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap with hq
  have hqc : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) q hqc
  set m : ℕ × ℕ := s.sup id
  refine ⟨m.1, m.2, ?_⟩
  set ι := schwartzJet (V := V) m.1 m.2
  have hbound : ∀ f, ‖T f‖ ≤ (C : ℝ) * ‖ι f‖ := by
    intro f
    have h1 : q f ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) f := hC f
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    have h2 : s.sup (schwartzSeminormFamily ℂ V ℂ) f ≤
        (Finset.Iic (m.1, m.2)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := by
      refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
      have hi' : i ∈ Finset.Iic (m.1, m.2) := Finset.mem_Iic.2 (Finset.le_sup (f := id) hi)
      exact Seminorm.le_finset_sup_apply (p := fun m : ℕ × ℕ => (SchwartzMap.seminorm ℂ m.1 m.2 : Seminorm ℂ (SchwartzMap V ℂ))) hi'
    calc ‖T f‖ = q f := rfl
      _ ≤ C * s.sup (schwartzSeminormFamily ℂ V ℂ) f := h1
      _ ≤ C * ‖ι f‖ := by
          gcongr
          exact h2.trans (sup_seminorm_le_norm_schwartzJet _ _ f)
  have hinj : Function.Injective ι := schwartzJet_injective _ _
  let e := LinearEquiv.ofInjective ι hinj
  let g0 : LinearMap.range ι →ₗ[ℂ] ℂ := T.toLinearMap ∘ₗ e.symm.toLinearMap
  have hg0 : ∀ y, ‖g0 y‖ ≤ (C : ℝ) * ‖y‖ := by
    intro y
    obtain ⟨f, rfl⟩ := e.surjective y
    simp only [g0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe]
    have : ‖e f‖ = ‖ι f‖ := by
      rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
    rw [this]
    exact hbound f
  obtain ⟨L, hL, -⟩ := exists_extension_norm_eq (LinearMap.range ι) (g0.mkContinuous C hg0)
  refine ⟨L, fun f => ?_⟩
  have := hL (e f)
  rw [LinearEquiv.ofInjective_apply] at this
  rw [this]
  simp [g0, e]

theorem clm_integral_exchange {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure W) (T : SchwartzMap V ℂ →L[ℂ] ℂ) (Φ : W → SchwartzMap V ℂ) (hΦc : Continuous Φ)
    (hΦ : ∀ k n : ℕ, ∃ C : ℝ, ∀ w x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Φ w) x‖ ≤ C * (1 + ‖w‖) ^ n)
    (φ : W → ℂ) (hφm : AEStronglyMeasurable φ μ) (hφ : ∀ n : ℕ, Integrable (fun w => (1 + ‖w‖) ^ n * ‖φ w‖) μ)
    (h : SchwartzMap V ℂ) (hh : ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n h x = ∫ w, φ w • iteratedFDeriv ℝ n (Φ w) x ∂μ) :
    T h = ∫ w, φ w * T (Φ w) ∂μ := by
  obtain ⟨K, N, L, hL⟩ := exists_jet_factor T
  haveI : ProperSpace W := FiniteDimensional.proper_real W
  haveI : SecondCountableTopology W := secondCountable_of_proper
  haveI : SecondCountableTopologyEither W (SchwartzJetSpace V N) := ⟨Or.inl ‹_›⟩
  choose C hC using hΦ
  set ι := schwartzJet (V := V) K N
  set B : ℝ := ∑ m ∈ Finset.Iic (K, N), |C m.1 m.2|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hjet : ∀ w, ‖ι (Φ w)‖ ≤ 2 ^ K * B * (1 + ‖w‖) ^ N := by
    intro w
    have h1w : (1 : ℝ) ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    refine (norm_schwartzJet_le K N (Φ w)).trans ?_
    rw [mul_assoc]
    gcongr
    refine Seminorm.finset_sup_apply_le (by positivity) fun m hm => ?_
    refine SchwartzMap.seminorm_le_bound ℂ m.1 m.2 (Φ w) (by positivity) fun x => ?_
    refine (hC m.1 m.2 w x).trans ?_
    have hm2 : m.2 ≤ N := (Finset.mem_Iic.1 hm).2
    calc C m.1 m.2 * (1 + ‖w‖) ^ m.2 ≤ |C m.1 m.2| * (1 + ‖w‖) ^ N :=
          mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1w hm2) (by positivity) (abs_nonneg _)
      _ ≤ B * (1 + ‖w‖) ^ N := by
          gcongr
          exact Finset.single_le_sum (f := fun m : ℕ × ℕ => |C m.1 m.2|) (fun _ _ => abs_nonneg _) hm
  have hιc : Continuous fun w => ι (Φ w) := (continuous_schwartzJet K N).comp hΦc
  set F : W → SchwartzJetSpace V N := fun w => φ w • ι (Φ w) with hF
  have hFint : Integrable F μ := by
    refine Integrable.mono' ((hφ N).const_mul (2 ^ K * B)) (hφm.smul hιc.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [hF, norm_smul]
    calc ‖φ w‖ * ‖ι (Φ w)‖ ≤ ‖φ w‖ * (2 ^ K * B * (1 + ‖w‖) ^ N) := by gcongr; exact hjet w
      _ = 2 ^ K * B * ((1 + ‖w‖) ^ N * ‖φ w‖) := by ring
  have hI : ι h = ∫ w, F w ∂μ := by
    funext n
    ext x : 1
    let ev := (BoundedContinuousFunction.evalCLM ℂ x).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun n : Fin (N + 1) => BoundedContinuousFunction V
        (ContinuousMultilinearMap ℝ (fun _ : Fin (n : ℕ) => V) ℂ)) n)
    have hev : ∀ y : SchwartzJetSpace V N, ev y = y n x := fun y => rfl
    rw [show ((∫ w, F w ∂μ) n) x = ev (∫ w, F w ∂μ) from rfl,
      ← ContinuousLinearMap.integral_comp_comm ev hFint]
    simp only [hev, hF, schwartzJet_apply, ι, Pi.smul_apply, BoundedContinuousFunction.coe_smul]
    rw [hh, ← integral_smul]
    congr 1
    funext w
    exact smul_comm _ _ _
  rw [hL h, hI, ← ContinuousLinearMap.integral_comp_comm L hFint]
  congr 1
  funext w
  simp only [hF, map_smul, smul_eq_mul, hL]

end

end GlobalTheory
