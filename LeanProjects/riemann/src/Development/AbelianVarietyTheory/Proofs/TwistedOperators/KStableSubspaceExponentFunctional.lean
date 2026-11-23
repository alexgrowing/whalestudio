import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutingIsometriesCommonEigenvectorStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IndFunctional

theorem exists_factor {A H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup H] [Module ℂ H]
    (ι : A →ₗ[ℂ] H) (L : A →ₗ[ℂ] ℂ) (hL : ∀ a, ι a = 0 → L a = 0) :
    ∃ ℓ : H →ₗ[ℂ] ℂ, ∀ a, ℓ (ι a) = L a := by
  have hle : LinearMap.ker ι ≤ LinearMap.ker L := fun a ha => hL a ha
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend
    (((LinearMap.ker ι).liftQ L hle).comp ι.quotKerEquivRange.symm.toLinearMap)
  refine ⟨ℓ, fun a => ?_⟩
  have := LinearMap.congr_fun hℓ ⟨ι a, LinearMap.mem_range_self ι a⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  rw [this]
  rfl

theorem apply_one_eq_zero {n : ℕ} {ε : Fin n → Bool} (I : IndModule ε) (f : I.fns) (hf : I.ι f = 0) :
    f.1 1 = 0 := by
  have hc : Continuous f.1 := (mem_indFun_top.1 f.2).1
  have hck : Continuous fun k : KG ε => ‖f.1 k‖ ^ 2 := (hc.comp continuous_subtype_val).norm.pow 2
  have hint : Integrable (fun k : KG ε => ‖f.1 k‖ ^ 2) (muK ε) :=
    hck.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∫ k : KG ε, ‖f.1 k‖ ^ 2 ∂muK ε = 0 := by
    rw [← I.model.norm_sq f, hf, norm_zero]; norm_num
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) hint).1 h0
  have heq : (fun k : KG ε => ‖f.1 k‖ ^ 2) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hck continuous_const).1 hae
  have := congrFun heq ⟨1, (KG ε).one_mem⟩
  simpa using this

theorem functional : GlobalTheory.Published.Langlands.Induced → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ H₀ T : Matrix (Fin n) (Fin n) ℂ, H₀ ∈ lieSet ε → T ∈ lieSet ε → (∀ x : ℝ, IsSplit ε I.W (Pi.single ⟨0, h⟩ x) (expG ε H₀ x)) → (∀ θ : ℝ, expG ε T θ ∈ KG ε ⊓ I.M ∧ ∀ m ∈ I.M, expG ε T θ * m = m * expG ε T θ) → ∀ Y : Submodule ℂ I.H, Y ≤ kFinVec ε I.ρ → Y ≠ ⊥ → IsKStableOn ε I.ρ Y → ∃ (ℓ : I.H →ₗ[ℂ] ℂ) (γ : ℂ), (∃ y ∈ Y, ℓ y ≠ 0) ∧ (∀ X ∈ lieSet ε, (∀ t, expG ε X t ∈ flagN ε I.W) → ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ X w) = 0) ∧ (∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ H₀ w) = (I.s ⟨0, h⟩ + n - 1) * ℓ w) ∧ ∀ w ∈ kFinVec ε I.ρ, ℓ (dRep I.ρ T w) = γ * ℓ w := by
  intro hInd n ε I h hj H₀ T hH₀ hT hsp hTθ Y hYk hY0 hYs
  obtain ⟨-, -, -, hkf, hder, -⟩ := hInd n ε I
  obtain ⟨hσ, -⟩ := I.temp.2.2
  have huM1 : uMat (1 : UJ ε) = 1 := rfl
  have hσ1 : I.σ 1 = 1 := hσ.1.1
  have hσmul : ∀ a ∈ I.M, ∀ b ∈ I.M, I.σ (uMat (a * b)) = (I.σ (uMat a)).comp (I.σ (uMat b)) :=
    fun a ha b hb => hσ.1.2 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hσiso : ∀ m ∈ I.M, ∀ x, ‖I.σ (uMat m) x‖ = ‖x‖ := fun m hm x => hσ.2.1 _ ⟨m, hm, rfl⟩ x
  have hinner : ∀ m ∈ I.M, ∀ a b, ⟪I.σ (uMat m) a, I.σ (uMat m) b⟫_ℂ = ⟪a, b⟫_ℂ := fun m hm a b =>
    (⟨(I.σ (uMat m)).toLinearMap, hσiso m hm⟩ : I.V →ₗᵢ[ℂ] I.V).inner_map_map a b
  have hN1 : (1 : UJ ε) ∈ flagN ε I.W := ⟨fun i y _ => by simp [huM1], fun y _ => by simp [huM1]⟩
  have law : ∀ f : I.fns, ∀ u ∈ flagN ε I.W, ∀ m ∈ I.M, ∀ x t, IsSplit ε I.W x t →
      f.1 (u * m * t) = Complex.exp (pairing I.j (I.s + rho n I.j) x) • I.σ (uMat m) (f.1 1) := by
    intro f u hu m hm x t ht
    simpa using (mem_indFun_top.1 f.2).2 u hu m hm x t ht 1
  have law0 : ∀ f : I.fns, ∀ u ∈ flagN ε I.W, ∀ m ∈ I.M, f.1 (u * m) = I.σ (uMat m) (f.1 1) := by
    intro f u hu m hm
    simpa [pairing] using law f u hu m hm 0 1 isSplit_one
  have kf : ∀ w ∈ kFinVec ε I.ρ, ∃ f : I.fns, IsKFinFun f.1 ∧ I.ι f = w := fun w hw => (hkf w).1 hw
  have dat1 : ∀ X ∈ lieSet ε, ∀ w ∈ kFinVec ε I.ρ, ∃ f f' : I.fns, I.ι f = w ∧ I.ι f' = dRep I.ρ X w ∧
      HasDerivAt (fun t : ℝ => f.1 (expG ε X t)) (f'.1 1) 0 := by
    intro X hX w hw
    obtain ⟨f, hfk, rfl⟩ := kf w hw
    obtain ⟨f', hd, he⟩ := hder f hfk X hX
    exact ⟨f, f', rfl, he.symm, by simpa using hd 1⟩

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  obtain ⟨f, hfk, rfl⟩ := kf y (hYk hyY)
  have hf0 : f.1 ≠ 0 := fun e => hy0 (by rw [show f = 0 from Subtype.ext e, map_zero])
  obtain ⟨k₀, hk₀, hfk₀⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum f.1 f.2 hfk).2.2 hf0
  let f₁ : I.fns := ⟨fun g => f.1 (g * k₀), indFun_mul_right f.2 trivial⟩
  have hf₁k : IsKFinFun f₁.1 := by
    have hle : Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f₁.1 (g * k)} ≤
        Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f.1 (g * k)} := by
      refine Submodule.span_mono ?_
      rintro φ ⟨k, hk, rfl⟩
      exact ⟨k * k₀, mul_mem hk hk₀, by funext g; simp [f₁, mul_assoc]⟩
    haveI : FiniteDimensional ℂ (Submodule.span ℂ {φ : UJ ε → I.V | ∃ k ∈ KG ε, φ = fun g => f.1 (g * k)}) := hfk
    exact Submodule.finiteDimensional_of_le hle
  have hy₁ : I.ρ (uMat k₀) (I.ι f) = I.ι f₁ := I.model.transl k₀ trivial f f₁ fun g => rfl
  have hy₁Y : I.ι f₁ ∈ Y := hy₁ ▸ hYs (uMat k₀) hk₀ _ hyY
  have hx₀ : f₁.1 1 ≠ 0 := by simpa [f₁] using hfk₀
  obtain ⟨U, hUfd, hx₀U, hUst⟩ := (GlobalTheory.T.induced_k_finite_restriction n ε I.toDatum f₁.1 f₁.2 hf₁k).2.1

  have hum : ∀ θ, (expG ε T θ)⁻¹ ∈ KG ε ⊓ I.M := fun θ => inv_mem (hTθ θ).1
  obtain ⟨v, -, hvx, hv⟩ := GlobalTheory.T.commuting_isometries_common_eigenvector U hUfd (fun θ => I.σ (uMat (expG ε T θ)⁻¹)) (f₁.1 1) hx₀U hx₀
    (fun θ x hx => hUst _ (hum θ) x hx) (fun θ x => hσiso _ (hum θ).2 x) (fun θ θ' x => by
      rw [← ContinuousLinearMap.comp_apply, ← hσmul _ (hum θ).2 _ (hum θ').2, ← ContinuousLinearMap.comp_apply,
        ← hσmul _ (hum θ').2 _ (hum θ).2, (Commute.inv_left ((hTθ θ).2 _ (hum θ').2)).eq])
  choose c hc using hv
  have key : ∀ θ x, ⟪v, I.σ (uMat (expG ε T θ)) x⟫_ℂ = starRingEnd ℂ (c θ) * ⟪v, x⟫_ℂ := by
    intro θ x
    have h1 : I.σ (uMat (expG ε T θ)⁻¹) (I.σ (uMat (expG ε T θ)) x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← hσmul _ (hum θ).2 _ (hTθ θ).1.2, inv_mul_cancel, huM1, hσ1]
      rfl
    rw [← hinner _ (hum θ).2, h1, hc θ, inner_smul_left]

  obtain ⟨ℓ, hℓ⟩ := exists_factor I.ι ((innerSL ℂ v).toLinearMap ∘ₗ (LinearMap.proj 1) ∘ₗ I.fns.subtype)
    (fun a ha => by simp [apply_one_eq_zero I a ha])
  have hℓ' : ∀ a : I.fns, ℓ (I.ι a) = ⟪v, a.1 1⟫_ℂ := fun a => by rw [hℓ]; rfl
  have hinD : ∀ {F : ℝ → I.V} {F' : I.V}, HasDerivAt F F' 0 → HasDerivAt (fun t => ⟪v, F t⟫_ℂ) ⟪v, F'⟫_ℂ 0 :=
    fun hF => (((innerSL ℂ v).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hF
  have lawT : ∀ (g : I.fns) θ, ⟪v, g.1 (expG ε T θ)⟫_ℂ = starRingEnd ℂ (c θ) * ⟪v, g.1 1⟫_ℂ := by
    intro g θ
    have := law0 g 1 hN1 _ (hTθ θ).1.2
    rw [one_mul] at this
    rw [this, key]

  obtain ⟨f₁', hd₁, -⟩ := hder f₁ hf₁k T hT
  set γ := ⟪v, f₁'.1 1⟫_ℂ / ⟪v, f₁.1 1⟫_ℂ
  have hg : HasDerivAt (fun θ : ℝ => starRingEnd ℂ (c θ)) γ 0 := by
    have := (hinD (by simpa using hd₁ 1)).div_const ⟪v, f₁.1 1⟫_ℂ
    have e : (fun θ : ℝ => starRingEnd ℂ (c θ)) = fun θ => ⟪v, f₁.1 (expG ε T θ)⟫_ℂ / ⟪v, f₁.1 1⟫_ℂ := by
      funext θ
      rw [lawT, mul_div_assoc, div_self hvx, mul_one]
    rw [e]
    exact this
  refine ⟨ℓ, γ, ⟨I.ι f₁, hy₁Y, by rw [hℓ']; exact hvx⟩, ?_, ?_, ?_⟩
  · intro X hX hXN w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 X hX w hw
    rw [← he, hℓ']
    have hconst : (fun t : ℝ => g.1 (expG ε X t)) = fun _ => g.1 1 := funext fun t => by
      simpa [huM1, hσ1] using law0 g _ (hXN t) 1 (one_mem _)
    rw [hconst] at hd
    rw [hd.unique (hasDerivAt_const _ _), inner_zero_right]
  · intro w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 H₀ hH₀ w hw
    rw [← he, hℓ', hℓ']
    have hIio : Finset.Iio (⟨0, h⟩ : Fin I.a) = ∅ := by
      ext l; simp [Fin.lt_iff_val_lt_val]
    have hpair : ∀ t : ℝ, pairing I.j (I.s + rho n I.j) (Pi.single ⟨0, h⟩ t) = (I.s ⟨0, h⟩ + n - 1) * t := by
      intro t
      rw [pairing, Finset.sum_eq_single ⟨0, h⟩]
      · simp [hj, rho, hIio]
        left; ring
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    have hfun : (fun t : ℝ => g.1 (expG ε H₀ t)) = fun t : ℝ => Complex.exp ((I.s ⟨0, h⟩ + n - 1) * t) • g.1 1 :=
      funext fun t => by
        have := law g 1 hN1 1 (one_mem _) _ _ (hsp t)
        rw [one_mul, one_mul, hpair, huM1, hσ1] at this
        simpa using this
    rw [hfun] at hd
    have hd' : HasDerivAt (fun t : ℝ => Complex.exp ((I.s ⟨0, h⟩ + n - 1) * t) • g.1 1)
        ((I.s ⟨0, h⟩ + n - 1) • g.1 1) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (I.s ⟨0, h⟩ + n - 1)).cexp).smul_const (g.1 1)
      simpa using this
    rw [hd.unique hd', inner_smul_right]
  · intro w hw
    obtain ⟨g, g', rfl, he, hd⟩ := dat1 T hT w hw
    rw [← he, hℓ', hℓ']
    have h2 := hinD hd
    have h3 : HasDerivAt (fun θ : ℝ => ⟪v, g.1 (expG ε T θ)⟫_ℂ) (γ * ⟪v, g.1 1⟫_ℂ) 0 := by
      have e : (fun θ : ℝ => ⟪v, g.1 (expG ε T θ)⟫_ℂ) = fun θ => starRingEnd ℂ (c θ) * ⟪v, g.1 1⟫_ℂ := by
        funext θ
        rw [lawT]
      rw [e]
      exact hg.mul_const ⟪v, g.1 1⟫_ℂ
    exact h2.unique h3

end GlobalTheory.IndFunctional
