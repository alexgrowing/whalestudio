import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.AddMemIffOfZero
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.KappaReal

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem memH {ε : AF F} (h : fixE ε) : ε * h.1 = h.1 := h.2

theorem memY {ε : AF F} (y : (AddMonoidHom.mulLeft ε).ker) : ε * y.1 = 0 := y.2

theorem kdata (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S')
    {ε : AF F} (hε : IsIdF S ε) (db : Measure (AF F)) (ν : Measure (fixE ε)) [SFinite ν]
    (νY : Measure (AddMonoidHom.mulLeft ε).ker) [SFinite νY] (c : ℝ≥0) (hc : 0 < c)
    (hdec : ∀ f : AF F → ℂ,
      (Integrable f db ↔ Integrable (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => f (z.1.1 + z.2.1)) (ν.prod νY)) ∧
      ∫ x, f x ∂db = (c : ℂ) * ∫ z : fixE ε × (AddMonoidHom.mulLeft ε).ker, f (z.1.1 + z.2.1) ∂(ν.prod νY))
    (ρ : Ainf F → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU0 : ∀ v, (0 : Fv F v) ∈ U v)
    (hI : Integrable (fouA ψ db (testT ρ S' U)) db)
    (hinv : ∀ z, ∫ b, fouA ψ db (testT ρ S' U) b * ψ (b * z) ∂db = testT ρ S' U (-z))
    (hne : ∫ y, testT ρ S' U y ∂db ≠ 0) :
    ∃ (g : fixE ε → ℂ) (Gc : ℝ), 0 ≤ Gc ∧ Integrable g ν ∧ (∀ h, ‖g h‖ ≤ 1) ∧
      (∀ s, ∫ h, g h * ψ (h.1 * s) ∂ν = ((Gc * tR ρ S' U (-(ε * s)) : ℝ) : ℂ)) ∧
      ∀ h : fixE ε, g h = fouA ψ db (testT ρ S' U) h.1 / ∫ y, testT ρ S' U y ∂db := by
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hεε := idF_mul hε
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set τH : fixE ε → ℂ := fun h => ((tR ρ S' U h.1 : ℝ) : ℂ) with hτH
  set τY : (AddMonoidHom.mulLeft ε).ker → ℂ := fun y => ((bR S' U y.1 : ℝ) : ℂ) with hτY
  set A : AF F → ℂ := fun s => ∫ h, τH h * ψ (h.1 * s) ∂ν with hA
  set Bf : AF F → ℂ := fun s => ∫ y, τY y * ψ (y.1 * s) ∂νY with hBf
  have hsplit : ∀ (h : fixE ε) (y : (AddMonoidHom.mulLeft ε).ker), testT ρ S' U (h.1 + y.1) = τH h * τY y := by
    intro h y
    rw [testT_eq, tR_split hSS hε ρ U hU0 (memH h) (memY y)]
    push_cast
    rfl
  have hpm : ∀ (h h0 : fixE ε) (y y0 : (AddMonoidHom.mulLeft ε).ker),
      (h.1 + y.1) * (h0.1 + y0.1) = h.1 * h0.1 + y.1 * y0.1 := by
    intro h h0 y y0
    have h1 : h.1 * y0.1 = 0 := fix_mul_ker hεε (memH h) (memY y0)
    have h2 : y.1 * h0.1 = 0 := by rw [mul_comm]; exact fix_mul_ker hεε (memH h0) (memY y)
    rw [add_mul, mul_add, mul_add, h1, h2, add_zero, zero_add]
  have hfou : ∀ (h0 : fixE ε) (y0 : (AddMonoidHom.mulLeft ε).ker),
      fouA ψ db (testT ρ S' U) (h0.1 + y0.1) = (c : ℂ) * (A h0.1 * Bf y0.1) := by
    intro h0 y0
    simp only [fouA]
    rw [(hdec _).2]
    congr 1
    rw [← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsplit, hpm, AddChar.map_add_eq_mul]
    ring
  have hint : ∫ y, testT ρ S' U y ∂db = (c : ℂ) * ((∫ h, τH h ∂ν) * ∫ y, τY y ∂νY) := by
    rw [(hdec _).2, ← integral_prod_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z.1 z.2)
  set IH := ∫ h, τH h ∂ν with hIH
  set IY := ∫ y, τY y ∂νY with hIY
  have hIH0 : IH ≠ 0 := fun h0 => hne (by rw [hint, h0, zero_mul, mul_zero])
  have hIY0 : IY ≠ 0 := fun h0 => hne (by rw [hint, h0, mul_zero, mul_zero])
  have hτHI : Integrable τH ν := by
    by_contra hn
    exact hIH0 (integral_undef hn)
  have hτR : Integrable (fun h : fixE ε => tR ρ S' U h.1) ν := by
    have := hτHI.norm
    refine this.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [hτH, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tR_nonneg hρ0 S' U _)
  set IHr := ∫ h, tR ρ S' U h.1 ∂ν with hIHr
  have hIHc : IH = (IHr : ℂ) := integral_ofReal
  have hIHr0 : 0 < IHr := by
    refine lt_of_le_of_ne (integral_nonneg fun h => tR_nonneg hρ0 S' U _) fun h0 => hIH0 ?_
    rw [hIHc, ← h0, Complex.ofReal_zero]
  have hA0 : A 0 = IH := by
    simp only [hA, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIH.symm
  have hB0 : Bf 0 = IY := by
    simp only [hBf, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIY.symm
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1

  have hAc : Continuous A := by
    refine continuous_of_dominated (bound := fun h => ‖τH h‖) (fun s => ?_) (fun s => ?_) hτHI.norm ?_
    · exact hτHI.aestronglyMeasurable.mul
        (hψ.1.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun h => by rw [norm_mul, hψn, mul_one]
    · exact Filter.Eventually.of_forall fun h => continuous_const.mul (hψ.1.comp (continuous_const.mul continuous_id))

  set IB := ∫ y, Bf y.1 ∂νY with hIB
  have hinvH : ∀ s, ε * s = s →
      ((tR ρ S' U (-s) : ℝ) : ℂ) = (c : ℂ) ^ 2 * IB * ∫ h, A h.1 * ψ (h.1 * s) ∂ν := by
    intro s hs
    have h1 := hinv s
    rw [(hdec _).2, testT_eq] at h1
    have h2 : ∀ z : fixE ε × (AddMonoidHom.mulLeft ε).ker,
        fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1) * ψ ((z.1.1 + z.2.1) * s) =
          ((c : ℂ) * (A z.1.1 * ψ (z.1.1 * s))) * Bf z.2.1 := by
      intro z
      have hz : z.2.1 * s = 0 := by rw [mul_comm]; exact fix_mul_ker hεε hs (memY z.2)
      rw [hfou, add_mul, hz, add_zero]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h2),
      integral_prod_mul (fun h : fixE ε => (c : ℂ) * (A h.1 * ψ (h.1 * s))) (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1),
      integral_const_mul] at h1
    rw [← h1]
    ring

  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : fixE ε, tR ρ S' U h₀.1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hIHr0.ne'
    rw [hIHr]
    simp [hn]
  have hIB0 : IB ≠ 0 := by
    intro h0
    have h1 := hinvH (-h₀.1) (by rw [mul_neg, memH h₀])
    rw [neg_neg, h0, mul_zero, zero_mul] at h1
    exact hh₀ (by exact_mod_cast h1)
  set κ : ℂ := ((c : ℂ) ^ 2 * IB)⁻¹ with hκ
  have hcB : (c : ℂ) ^ 2 * IB ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) hIB0
  have hinvG : ∀ s, ∫ h, A h.1 * ψ (h.1 * s) ∂ν = κ * ((tR ρ S' U (-(ε * s)) : ℝ) : ℂ) := by
    intro s
    have hes : ε * (ε * s) = ε * s := by rw [← mul_assoc, hεε]
    have h1 : ∀ h : fixE ε, h.1 * s = h.1 * (ε * s) := fun h => by
      conv_lhs => rw [← memH h]
      ring
    simp only [h1]
    rw [hinvH _ hes, hκ, ← mul_assoc, inv_mul_cancel₀ hcB, one_mul]

  have hAI : Integrable (fun h : fixE ε => A h.1) ν := by
    have h1 := (hdec (fouA ψ db (testT ρ S' U))).1.1 hI
    have h2 : (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1)) =
        fun z => (c : ℂ) * (A z.1.1 * Bf z.2.1) := funext fun z => hfou z.1 z.2
    rw [h2] at h1
    have hBI : Integrable (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1) νY := by
      by_contra hn
      exact hIB0 (integral_undef hn)
    have hK : 0 < ∫ y, ‖Bf y.1‖ ∂νY :=
      lt_of_lt_of_le (norm_pos_iff.2 hIB0) (norm_integral_le_integral_norm _)
    have h3 := ((integrable_prod_iff h1.aestronglyMeasurable).1 h1).2
    have h4 : ∀ h : fixE ε, ∫ y, ‖(c : ℂ) * (A h.1 * Bf y.1)‖ ∂νY =
        (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY) * ‖A h.1‖ := by
      intro h
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_const_mul]
      ring
    simp only [h4] at h3
    have hcK : ‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY ≠ 0 := mul_ne_zero (norm_ne_zero_iff.2 hc0) hK.ne'
    have h5 : Integrable (fun h : fixE ε => ‖A h.1‖) ν := by
      refine (h3.const_mul (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY)⁻¹).congr (Filter.Eventually.of_forall fun h => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hcK, one_mul]
    exact (integrable_norm_iff (hAc.comp continuous_subtype_val).aestronglyMeasurable).1 h5

  obtain ⟨M, hM⟩ := hρc.bddAbove_range_of_hasCompactSupport hρs
  have hτM : ∀ h : fixE ε, tR ρ S' U h.1 ≤ M := by
    intro h
    have hρM : ρ (fstA F h.1) ≤ M := hM ⟨_, rfl⟩
    unfold tR
    by_cases hb : sndA F h.1 ∈ boxA S' U
    · rw [Set.indicator_of_mem hb, mul_one]; exact hρM
    · rw [Set.indicator_of_notMem hb, mul_zero]; exact (hρ0 _).trans hρM
  have hk := kappa_real ψ hψ ν (fun h => tR ρ S' U h.1) (fun h => tR_nonneg hρ0 S' U _) hτR hIHr0 M hτM
    (fun h => A h.1) (fun s => rfl) hAI κ (fun s => by
      have := hinvG s.1
      rw [memH s] at this
      exact this)
  have hAb : ∀ s, ‖A s‖ ≤ IHr := by
    intro s
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [hIHr]
    congr 1
    funext h
    rw [norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_of_nonneg (tR_nonneg hρ0 S' U _)]
  have hκr : κ = (κ.re : ℂ) := Complex.ext (by simp) (by simp [hk.1])
  have hIHr0' : (IHr : ℂ) ≠ 0 := by exact_mod_cast hIHr0.ne'
  refine ⟨fun h => A h.1 / IH, κ.re / IHr, div_nonneg hk.2 hIHr0.le, hAI.div_const _, fun h => ?_, fun s => ?_,
    fun h => ?_⟩
  · rw [norm_div, hIHc, Complex.norm_real, Real.norm_of_nonneg hIHr0.le]
    exact (div_le_one hIHr0).2 (hAb _)
  · simp_rw [div_mul_eq_mul_div]
    rw [integral_div, hinvG, hIHc, hκr]
    push_cast
    field_simp
    rw [Complex.ofReal_re]
    ring
  · have h1 := hfou h 0
    rw [ZeroMemClass.coe_zero, add_zero, hB0] at h1
    simp only
    rw [h1, hint]
    field_simp

end PositivityTheory.Rg.Rsw.L.LApproxId

end
