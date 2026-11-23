import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.TruncSB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SideEst
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem pw_mul {a b M R b' : ℝ} {d : ℕ} (ha : a ≤ M ^ (d + 1)) (hb0 : 0 ≤ b) (hb : b ≤ b') (h1 : 1 ≤ b')
    (hM : |M| ≤ R) : a * b ≤ (R * b') ^ (d + 1) := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hM
  have h2 : a ≤ R ^ (d + 1) :=
    ha.trans ((le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hM _))
  rw [mul_pow]
  exact mul_le_mul h2 (hb.trans (le_self_pow₀ h1 (Nat.succ_ne_zero d))) hb0 (by positivity)

private theorem exp_grow {B c₁ : ℝ} {j m' s₀ : ℕ} (hB0 : 0 ≤ B) (hB : B ≤ Real.exp c₁) (hc : 0 ≤ c₁) (hm : m' ≤ s₀) :
    B ^ (j + m') ≤ Real.exp (c₁ * s₀) * Real.exp (c₁ * j) := by
  refine (pow_le_pow_left₀ hB0 hB _).trans ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : (m' : ℝ) ≤ s₀ := by exact_mod_cast hm
  push_cast
  nlinarith

private theorem main_est {C₁ cU M₁ C₂ N c₁ η e1 e2 W D : ℝ} {N₀ j k m m' s₀ : ℕ} (hcU : 1 ≤ cU) (hM₁ : 4 ≤ M₁)
    (hη : 0 < η) (hη1 : η ≤ 1) (hk : k ≤ j) (hm : m ≤ s₀) (hm' : m' ≤ s₀) (h10 : 0 ≤ e1) (h1 : e1 ≤ W) (h20 : 0 ≤ e2)
    (h2 : e2 ≤ W / D) (hD : 0 < D) (hc : 0 ≤ c₁) (hA : cU * Real.exp (N₀ * C₂) ≤ Real.exp c₁)
    (hB : cU * (M₁ / 4) * Real.exp (-2 * C₂) ≤ Real.exp (-|N|)) :
    C₁ * cU ^ (j + m') * (Real.exp (N₀ * (C₂ * ((j + m' : ℕ) : ℝ))) * (e1 + (4 / η) ^ (k + m) * e2) +
        (4 / η) ^ (k + m) * Real.exp (-(((2 : ℕ) : ℝ) * (C₂ * ((j + m' : ℕ) : ℝ)))) * e1 +
        (M₁ / η) ^ (k + m) * W * Real.exp (-2 * (C₂ * ((j + m' : ℕ) : ℝ)))) ≤
      (2 * |C₁| * Real.exp (c₁ * s₀) * (M₁ / η) ^ s₀) * W *
        (Real.exp (c₁ * j) * (1 + (4 / η) ^ k / D) + (4 / η) ^ k * Real.exp (-N * j)) := by
  have hW : 0 ≤ W := h10.trans h1
  have hq : 1 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have hr : 1 ≤ M₁ / 4 := by linarith
  have hrq : M₁ / η = M₁ / 4 * (4 / η) := by field_simp
  rw [hrq]
  generalize 4 / η = q at *
  generalize M₁ / 4 = r at *
  have hrq1 : 1 ≤ r * q := one_le_mul_of_one_le_of_one_le hr hq
  have hR1 : (r * q) ^ m ≤ (r * q) ^ s₀ := pow_le_pow_right₀ hrq1 hm
  have hR2 : q ^ m ≤ (r * q) ^ s₀ := (pow_le_pow_left₀ (by linarith) (by nlinarith) m).trans hR1
  have hR3 : 1 ≤ (r * q) ^ s₀ := one_le_pow₀ hrq1
  have a1 : cU ^ (j + m') * Real.exp (N₀ * (C₂ * ((j + m' : ℕ) : ℝ))) ≤ Real.exp (c₁ * s₀) * Real.exp (c₁ * j) := by
    refine le_trans (le_of_eq ?_) (exp_grow (by positivity) hA hc hm')
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have a2 : cU ^ (j + m') * r ^ k * Real.exp (-2 * (C₂ * ((j + m' : ℕ) : ℝ))) ≤ Real.exp (-N * j) := by
    have b1 : r ^ k ≤ r ^ (j + m') := pow_le_pow_right₀ hr (by omega)
    have b2 : (cU * r * Real.exp (-2 * C₂)) ^ (j + m') ≤ Real.exp (-|N|) ^ (j + m') :=
      pow_le_pow_left₀ (by positivity) hB _
    have b3 : Real.exp (-|N|) ^ (j + m') ≤ Real.exp (-N * j) := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have := le_abs_self N
      have := abs_nonneg N
      have : (0 : ℝ) ≤ j := by positivity
      have : (0 : ℝ) ≤ m' := by positivity
      push_cast
      nlinarith
    refine le_trans ?_ (b2.trans b3)
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    have : ((j + m' : ℕ) : ℝ) * (-2 * C₂) = -2 * (C₂ * ((j + m' : ℕ) : ℝ)) := by ring
    rw [this]
    gcongr
  have hE : 1 ≤ Real.exp (c₁ * s₀) := Real.one_le_exp (by positivity)
  have e : -(((2 : ℕ) : ℝ) * (C₂ * ((j + m' : ℕ) : ℝ))) = -2 * (C₂ * ((j + m' : ℕ) : ℝ)) := by push_cast; ring
  rw [e]
  have p1 := Real.exp_pos (N₀ * (C₂ * ((j + m' : ℕ) : ℝ)))
  have p2 := Real.exp_pos (-2 * (C₂ * ((j + m' : ℕ) : ℝ)))
  have p3 := Real.exp_pos (c₁ * j)
  have p4 := Real.exp_pos (-N * j)
  generalize Real.exp (N₀ * (C₂ * ((j + m' : ℕ) : ℝ))) = x1 at *
  generalize Real.exp (-2 * (C₂ * ((j + m' : ℕ) : ℝ))) = x2 at *
  generalize Real.exp (c₁ * j) = x3 at *
  generalize Real.exp (-N * j) = x4 at *
  generalize Real.exp (c₁ * s₀) = E at *
  have hu : 0 ≤ cU ^ (j + m') := by positivity
  generalize cU ^ (j + m') = u at *
  have hrk : 1 ≤ r ^ k := one_le_pow₀ hr
  have hrqm : 0 ≤ (r * q) ^ m := by positivity
  rw [pow_add q, pow_add (r * q), mul_pow r q k]
  have hqk : 0 ≤ q ^ k := by positivity
  have hqm : 0 ≤ q ^ m := by positivity
  generalize q ^ k = qk at *
  generalize q ^ m = qm at *
  generalize r ^ k = rk at *
  generalize (r * q) ^ m = Rm at *
  generalize (r * q) ^ s₀ = R at *
  have a3 : u * x2 ≤ x4 := le_trans (by nlinarith [mul_nonneg hu p2.le]) a2
  have t1 : u * x1 * (e1 + qk * qm * e2) ≤ E * x3 * (R * W + qk * R * (W / D)) := by
    have : e1 ≤ R * W := h1.trans (le_mul_of_one_le_left hW hR3)
    gcongr
  have t2 : u * x2 * (qk * qm * e1) ≤ x4 * (qk * R * W) := by gcongr
  have t3 : u * rk * x2 * (qk * Rm * W) ≤ x4 * (qk * R * W) := by gcongr
  have t4 : x4 * (qk * R * W) ≤ E * (x4 * (qk * R * W)) := le_mul_of_one_le_left (by positivity) hE
  have t5 : 0 ≤ E * x3 * (R * W + qk * R * (W / D)) := by positivity
  calc _ = C₁ * (u * x1 * (e1 + qk * qm * e2) + u * x2 * (qk * qm * e1) + u * rk * x2 * (qk * Rm * W)) := by ring
    _ ≤ |C₁| * (u * x1 * (e1 + qk * qm * e2) + u * x2 * (qk * qm * e1) + u * rk * x2 * (qk * Rm * W)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C₁| * (2 * (E * x3 * (R * W + qk * R * (W / D))) + 2 * (E * (x4 * (qk * R * W)))) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = _ := by ring

private theorem tr_bd {E : Type} [Field E] [NumberField E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ}
    {𝔢 : Side θ 2} (𝔣 : Fam 𝔢) (N : Eu 𝔣.d' ≃ₗᵢ[ℂ] Eu 𝔣.d) (x : ℝ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ j, ‖𝔣.tr N x j‖ ≤ Ct * (‖𝔣.u 0 0‖ + 1) ^ j := by
  let Ψ : (Eu 𝔣.d' →L[ℂ] Eu 𝔣.d') →ₗ[ℂ] ℂ :=
    { toFun := fun a => LinearMap.trace ℂ (Eu 𝔣.d) ((N.toLinearEquiv : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d) ∘ₗ
        ((eigP 𝔣.a₀ x ∘L a ∘L symb 𝔣.βg 0 : Eu 𝔣.d' →L[ℂ] Eu 𝔣.d') : Eu 𝔣.d' →ₗ[ℂ] Eu 𝔣.d') ∘ₗ
        (𝔣.s.toLinearEquiv : Eu 𝔣.d →ₗ[ℂ] Eu 𝔣.d'))
      map_add' := fun a b => by
        rw [← map_add]; congr 1; ext v; simp
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul]; congr 1; ext v; simp }
  refine ⟨‖LinearMap.toContinuousLinearMap Ψ‖, norm_nonneg _, fun j => ?_⟩
  refine ((LinearMap.toContinuousLinearMap Ψ).le_opNorm (𝔣.u 0 0 ^ j)).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))

set_option maxHeartbeats 6000000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.sideEstX :
    OneSideX → EvVal → TruncSpec → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
      (μ : Measure (normOneGL K (2 + 2))) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ 2) (𝔵 : Fam 𝔰)
      (ev : PR K (2 + 2) →+* (LL μ →L[ℂ] LL μ)) (evz : ℂ → PR K (2 + 2) →+* (Eu 𝔵.d' →L[ℂ] Eu 𝔵.d'))
      (Nn : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d) (Cf : ℝ), 𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → 𝔵.IsEvz ev evz →
      Family μ 𝔵.A 𝔵.A' 0 𝔵.P Nn Cf → ∀ sp : Finset ℝ,
      (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥) →
      ∀ C₀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) ∧
        ∀ Φ G, admitted 𝔰.S Φ → IsGen Φ G →
          (∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ - 𝔵.P)‖ ≤ C ^ (d + 1) / d.factorial) →
          ∀ P : PR K (2 + 2), (∀ y ∈ P.vars, y.1 ∉ 𝔰.S) → ∃ (u : ℝ × Submodule ℂ (LL μ) → ℕ → ℂ) (w : ℝ → ℕ → ℂ),
            (∀ y ∈ s, ∀ (L : Ix K (2 + 2) → ℂ) t, At μ 𝔰.S y.2 (msOf L) t →
              Tendsto (u y) atTop (𝓝 (y.1 * val y.1 (msOf L) t P * evK L (hval t) Φ))) ∧
            (∀ (x : ℝ) (L : Ix K (2 + 2) → ℂ), msOf L = 𝔵.Λ → Tendsto (w x) atTop (𝓝 (x * val x 𝔵.Λ 𝔵.t P * evK L (hval 𝔵.t) Φ))) ∧
            ∀ p : ℕ, 0 < p → ∀ s₀ : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ j : ℕ in atTop, ∀ d : ℕ, ∀ m ≤ s₀, ∀ m' ≤ s₀, ∀ f : TG K (2 + 2),
              𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (C₀ * ((j + m' : ℕ) : ℝ))) f →
              ‖twInt θ f - ∑ y ∈ s, u y d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
                  trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) -
                ∑ x ∈ sp.filter (η < ·), w x d * (x : ℂ) ^ d * (cheb η (j / p + m) x : ℂ) * ((1 / 2 : ℂ) * 𝔵.tr Nn x (j + m'))‖ ≤
                M ^ (d + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) := by
  intro h1 hV hT K _ _ _ μ _ θ 𝔰 𝔵 ev evz Nn Cf hev hin hz hF sp hsp C₀ N
  classical
  obtain ⟨c, cU, M₁, N₀, hc, hcU, hM₁, H⟩ := h1 K μ θ 𝔰 𝔵 ev evz Nn Cf hev hin hz hF sp hsp
  obtain ⟨C₂, hC1, hC2, hC3⟩ : ∃ C₂ : ℝ, 1 ≤ C₂ ∧ C₀ ≤ c * C₂ ∧
      cU * (M₁ / 4) * Real.exp (-2 * C₂) ≤ Real.exp (-|N|) := by
    have hpos : 0 < cU * (M₁ / 4) := by positivity
    have q1 : 0 ≤ |C₀| / c := by positivity
    have q2 := abs_nonneg N
    refine ⟨1 + |C₀| / c + |N| + cU * (M₁ / 4), by linarith, ?_, ?_⟩
    · have : c * (|C₀| / c) = |C₀| := by field_simp
      have := le_abs_self C₀
      nlinarith
    · have q3 : cU * (M₁ / 4) ≤ Real.exp (cU * (M₁ / 4)) := by linarith [Real.add_one_le_exp (cU * (M₁ / 4))]
      refine (mul_le_mul_of_nonneg_right q3 (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c₁, hc0, hcA, hcB⟩ : ∃ c₁ : ℝ, 0 ≤ c₁ ∧ cU * Real.exp (N₀ * C₂) ≤ Real.exp c₁ ∧
      ‖𝔵.u 0 0‖ + 1 ≤ Real.exp c₁ := by
    have q1 : 0 ≤ cU * Real.exp (N₀ * C₂) := by positivity
    have q2 := norm_nonneg (𝔵.u 0 0)
    have q3 := Real.add_one_le_exp (cU * Real.exp (N₀ * C₂) + ‖𝔵.u 0 0‖)
    exact ⟨cU * Real.exp (N₀ * C₂) + ‖𝔵.u 0 0‖, by linarith, by linarith, by linarith⟩
  refine ⟨c₁, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  obtain ⟨s, hs, hfin, H⟩ := H η hη hη1 χ hχ hχ1 hχ2
  obtain ⟨C₁, T₁, H⟩ := H 2
  refine ⟨s, hs, hfin, fun Φ G hΦ hG hC P hP => ?_⟩
  obtain ⟨Ck, hC⟩ := hC
  obtain ⟨⟨κ, D, hκ, hBd⟩, hval', hnorm⟩ := (hT K (2 + 2) 𝔰.S Φ hΦ).2 G hG
  obtain ⟨Me, hMe⟩ := hnorm (LL μ) ev hev.const
  have hSB : ∀ R : PR K (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔰.S) → ∃ M, SB (fun z => evz z R) M := fun R hR =>
    ((actLaws 𝔵.A'.J).2.2.1 _ _ (hz.act R hR)).1
  obtain ⟨Mt, hMt⟩ := truncSB evz hz.const 𝔰.S hSB Φ G hΦ hG
  obtain ⟨KP, hKP⟩ := hSB P hP
  have htv : ∀ d, ∀ y ∈ (trunc d G).vars, y.1 ∉ 𝔰.S := fun d y hy => hκ _ ((hBd d).1 y hy)
  have hQv : ∀ d, ∀ y ∈ (trunc d G * P).vars, y.1 ∉ 𝔰.S := fun d y hy => by
    rcases Finset.mem_union.mp (vars_mul _ _ hy) with h | h
    · exact htv d y h
    · exact hP y h
  have hV' := fun y (hy : y ∈ s) =>
    hV K (2 + 2) (by norm_num) μ 𝔰.toAmp y.2 y.1 (hη.trans ((hs y).1 hy).1) ((hs y).1 hy).2.1
  have hex : ∀ y : ℝ × Submodule ℂ (LL μ), ∃ Λ t, y ∈ s → At μ 𝔰.S y.2 Λ t := fun y => by
    by_cases hy : y ∈ s
    · obtain ⟨Λ, t, h⟩ := (hV' y hy).1 ((hs y).1 hy).2.2.2
      exact ⟨Λ, t, fun _ => h⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun h => absurd h hy⟩
  choose Λ t hΛ using hex
  have huniq : ∀ y ∈ s, ∀ Λ' t', At μ 𝔰.S y.2 Λ' t' → ∀ R : PR K (2 + 2), (∀ y ∈ R.vars, y.1 ∉ 𝔰.S) →
      val y.1 (Λ y) (t y) R = val y.1 Λ' t' R := fun y hy Λ' t' h R hR => by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hs y).1 hy).2.2.2
    have e1 := (hV' y hy).2.2 ev hev _ _ (hΛ y hy) R hR v hv
    have e2 := (hV' y hy).2.2 ev hev _ _ h R hR v hv
    exact smul_left_injective ℂ hv0 (e1.symm.trans e2)
  refine ⟨fun y d => y.1 * val y.1 (Λ y) (t y) P * (val y.1 (Λ y) (t y) (trunc d G) / (y.1 : ℂ) ^ d),
    fun x d => x * val x 𝔵.Λ 𝔵.t P * (val x 𝔵.Λ 𝔵.t (trunc d G) / (x : ℂ) ^ d), ?_, ?_, ?_⟩
  · intro y hy L t' h
    obtain ⟨u, hu, hu'⟩ := hval' L t'
    have hy0 : (y.1 : ℂ) ≠ 0 := by exact_mod_cast (hη.trans ((hs y).1 hy).1).ne'
    refine (hu.const_mul _).congr fun d => ?_
    beta_reduce
    rw [huniq y hy _ _ h P hP, huniq y hy _ _ h _ (htv d), hu', mul_div_cancel_left₀ _ (pow_ne_zero d hy0)]
  · intro x L hL
    obtain ⟨u, hu, hu'⟩ := hval' L 𝔵.t
    rw [hL] at hu'
    refine (hu.const_mul _).congr fun d => ?_
    beta_reduce
    by_cases hx : (x : ℂ) = 0
    · simp [hx]
    · rw [hu', mul_div_cancel_left₀ _ (pow_ne_zero d hx)]
  intro p hp s₀
  choose Ct hCt0 hCt using fun x => tr_bd 𝔵 Nn x
  obtain ⟨M₀, hM₀0, hM₀⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ {a b M : ℝ} {d : ℕ}, a ≤ M ^ (d + 1) → 0 ≤ b → b ≤ ‖ev P‖ + |KP| + 1 →
      |M| ≤ |Me| + |Ck| + |Mt| + 1 → a * b ≤ M₀ ^ (d + 1) :=
    ⟨(|Me| + |Ck| + |Mt| + 1) * (‖ev P‖ + |KP| + 1), by positivity, fun ha hb hb' hM =>
      pw_mul ha hb hb' (by linarith [norm_nonneg (ev P), abs_nonneg KP]) hM⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 2 * |C₁| * Real.exp (c₁ * s₀) * (M₁ / η) ^ s₀ := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = (∑ x ∈ sp, Ct x) * Real.exp (c₁ * s₀) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ M₁ := by linarith
    rw [hK₁]; positivity
  have hS0 : 0 ≤ ∑ x ∈ sp, Ct x := Finset.sum_nonneg fun x _ => hCt0 x
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨(K₁ + K₂ + 1) * M₀, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈T₁⌉₊] with j hj d m hm m' hm' f hf
  have n1 := abs_nonneg Me
  have n2 := abs_nonneg Ck
  have n3 := abs_nonneg Mt
  have n4 := abs_nonneg KP
  have n5 := norm_nonneg (ev P)
  have hW0 : 0 ≤ M₀ ^ (d + 1) := by positivity
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have b1 : ‖ev (trunc d G * P)‖ ≤ M₀ ^ (d + 1) := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (hM₀ (hMe d) n5 (by linarith) (by linarith))
  have b2 : ‖ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ - 𝔵.P)‖ ≤ M₀ ^ (d + 1) / d.factorial := by
    rw [mul_comm, map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, le_div_iff₀ hfac]
    have := (le_div_iff₀ hfac).mp (hC d)
    refine le_trans ?_ (hM₀ this n5 (by linarith) (by linarith))
    rw [mul_right_comm, mul_comm _ ‖ev P‖]
    exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) hfac.le
  have b3 : SB (fun z => evz z (trunc d G * P)) (M₀ ^ (d + 1)) := fun z hz' => by
    simp only [map_mul]
    exact (norm_mul_le _ _).trans (hM₀ (hMt d z hz') (norm_nonneg _)
      ((hKP z hz').trans (by linarith [le_abs_self KP])) (by linarith))
  have hj0 : (0 : ℝ) ≤ ((j + m' : ℕ) : ℝ) := by positivity
  have hT₁ : T₁ ≤ C₂ * ((j + m' : ℕ) : ℝ) := by
    have q1 : T₁ ≤ ((j + m' : ℕ) : ℝ) := (Nat.le_ceil T₁).trans (by exact_mod_cast hj.trans (Nat.le_add_right _ _))
    nlinarith
  have hf' : 𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (c * (C₂ * ((j + m' : ℕ) : ℝ)))) f :=
    ⟨hf.1, fun x hx => hf.2 x (lt_of_le_of_lt (Real.exp_le_exp.mpr (by nlinarith)) hx)⟩
  have E1 := (H (trunc d G * P) (fun y => val y.1 (Λ y) (t y) (trunc d G * P)) _ (hQv d) b3
    (fun y hy v hv => (hV' y hy).2.2 ev hev _ _ (hΛ y hy) _ (hQv d) v hv) (j / p + m) (j + m') _ f hT₁ hf').trans
    (main_est hcU hM₁ hη hη1 (Nat.div_le_self j p) hm hm' (norm_nonneg _) b1 (norm_nonneg _) b2 hfac hc0 hcA hC3)
  have E2 : ‖(1 / 2 : ℂ) * ∑ x ∈ sp.filter (fun x => ¬ η < x), (cheb η (j / p + m) x : ℂ) *
      (x * val x 𝔵.Λ 𝔵.t (trunc d G * P) * 𝔵.tr Nn x (j + m'))‖ ≤ K₂ * M₀ ^ (d + 1) * Real.exp (c₁ * j) := by
    have g1 : ∀ x ∈ sp.filter (fun x => ¬ η < x), ‖(cheb η (j / p + m) x : ℂ) *
        (x * val x 𝔵.Λ 𝔵.t (trunc d G * P) * 𝔵.tr Nn x (j + m'))‖ ≤
        Ct x * (M₀ ^ (d + 1) * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j))) := by
      intro x hx
      obtain ⟨hx, hxη⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx0, hx⟩ := (hsp x).1 hx
      have hxη : x ≤ η := not_lt.mp hxη
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      have r1 : ‖(cheb η (j / p + m) x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real]; exact (UpperTheory.ConvolutionTheory.FX.cheb_bound η _ hη hη1).1 x ⟨hx0.le, hxη⟩
      have r2 : ‖(x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]; linarith
      have r3 : ‖val x 𝔵.Λ 𝔵.t (trunc d G * P)‖ ≤ M₀ ^ (d + 1) := by
        have q1 := (evz 0 (trunc d G * P)).le_of_opNorm_le (b3 0 (by simp)) v
        rw [hz.zero _ (hQv d) x hx0 v hv, norm_smul] at q1
        exact le_of_mul_le_mul_right q1 (norm_pos_iff.mpr hv0)
      have r4 : ‖𝔵.tr Nn x (j + m')‖ ≤ Ct x * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j)) :=
        (hCt x _).trans (mul_le_mul_of_nonneg_left (exp_grow (by positivity) hcB hc0 hm') (hCt0 x))
      have := hCt0 x
      rw [norm_mul, norm_mul, norm_mul]
      calc _ ≤ 1 * (1 * M₀ ^ (d + 1) * (Ct x * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j)))) := by gcongr
        _ = _ := by ring
    have g2 := (norm_sum_le _ _).trans (Finset.sum_le_sum g1)
    rw [← Finset.sum_mul] at g2
    have g3 : ∑ x ∈ sp.filter (fun x => ¬ η < x), Ct x ≤ ∑ x ∈ sp, Ct x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hCt0 x
    rw [norm_mul]
    have g4 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
    calc _ ≤ 1 * ((∑ x ∈ sp, Ct x) * (M₀ ^ (d + 1) * (Real.exp (c₁ * s₀) * Real.exp (c₁ * j)))) :=
          mul_le_mul g4 (g2.trans (by gcongr)) (norm_nonneg _) zero_le_one
      _ = _ := by rw [hK₂]; ring
  have s1 : ∑ y ∈ s, y.1 * val y.1 (Λ y) (t y) P * (val y.1 (Λ y) (t y) (trunc d G) / (y.1 : ℂ) ^ d) * (y.1 : ℂ) ^ d *
        (cheb η (j / p + m) y.1 : ℂ) * trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) =
      ∑ y ∈ s, (cheb η (j / p + m) y.1 : ℂ) * (y.1 * val y.1 (Λ y) (t y) (trunc d G * P) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy0 : (y.1 : ℂ) ≠ 0 := by exact_mod_cast (hη.trans ((hs y).1 hy).1).ne'
    rw [map_mul]
    field_simp
  have s2 : ∑ x ∈ sp.filter (η < ·), x * val x 𝔵.Λ 𝔵.t P * (val x 𝔵.Λ 𝔵.t (trunc d G) / (x : ℂ) ^ d) * (x : ℂ) ^ d *
        (cheb η (j / p + m) x : ℂ) * ((1 / 2 : ℂ) * 𝔵.tr Nn x (j + m')) =
      (1 / 2 : ℂ) * ∑ x ∈ sp.filter (η < ·), (cheb η (j / p + m) x : ℂ) *
        (x * val x 𝔵.Λ 𝔵.t (trunc d G * P) * 𝔵.tr Nn x (j + m')) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hη.trans (Finset.mem_filter.mp hx).2).ne'
    rw [map_mul]
    field_simp
  rw [← Finset.sum_filter_add_sum_filter_not sp (η < ·), mul_add, ← sub_sub, ← hK₁] at E1
  beta_reduce
  rw [s1, s2]
  have hq : 0 ≤ (4 / η) ^ (j / p) := by positivity
  have x3 := Real.exp_pos (c₁ * j)
  have x4 := Real.exp_pos (-N * j)
  have F0 : Real.exp (c₁ * j) ≤
      Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j) := by
    have : 0 ≤ Real.exp (c₁ * j) * ((4 / η) ^ (j / p) / d.factorial) := by positivity
    have : 0 ≤ (4 / η) ^ (j / p) * Real.exp (-N * j) := by positivity
    linarith
  have F1 := x3.le.trans F0
  refine (norm_le_norm_sub_add _ _).trans ((add_le_add E1 (E2.trans (mul_le_mul_of_nonneg_left F0 (by positivity)))).trans ?_)
  rw [← add_mul, ← add_mul, mul_pow]
  have F2 : K₁ + K₂ ≤ (K₁ + K₂ + 1) ^ (d + 1) := le_trans (by linarith) (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
  gcongr
