import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AutomorphicArithmetic.DivisorFrames.FourierSchwartzBruhatPreserved
import Development.AutomorphicArithmetic.DivisorFrames.FourierTransformPairingTranslate
import Development.AutomorphicArithmetic.DivisorFrames.LocalUnitsHaarComparison
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

open scoped Pointwise in

private theorem UpperTheory.haar_integral_character_twist {G A : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Monoid A] [TopologicalSpace A] [ContinuousMul A] (μ : Measure G) [μ.IsHaarMeasure]
    (j : G → A) (hj : Continuous j) (hjm : ∀ x y, j (x * y) = j x * j y)
    (χ : G → ℂ) (hχ : Continuous χ) (hχm : ∀ x y, χ (x * y) = χ x * χ y) (hχ0 : ∀ x, χ x ≠ 0)
    (hint : ∀ K : Set A, IsCompact K → Integrable (fun l => K.indicator (fun _ => ‖χ l‖) (j l)) μ)
    (T : A → ℂ) (hT : Continuous T) (hTc : HasCompactSupport T)
    (g : G → ℂ) (hg : Continuous g) (C : Set G) (hC : IsCompact C) (hgC : ∀ x, g x ≠ 0 → x ∈ C) :
    (∫ y, T (j y) * χ y ∂μ) * (∫ x, g x * (χ x)⁻¹ ∂μ) = ∫ y, χ y * ∫ x, g x * T (j x * j y) ∂μ ∂μ := by
  have h1 : ∀ x, (∫ y, T (j y) * χ y ∂μ) * (g x * (χ x)⁻¹) = ∫ y, χ y * (g x * T (j x * j y)) ∂μ := by
    intro x
    rw [← integral_mul_left_eq_self (fun y => T (j y) * χ y) x, ← integral_mul_const]
    congr 1
    funext y
    rw [hjm, hχm]
    have := hχ0 x
    field_simp
  obtain ⟨M, hM⟩ := hT.bounded_above_of_compact_support hTc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hK : IsCompact ((j '' C⁻¹) * tsupport T) := (hC.inv.image hj).mul hTc
  have hgi : Integrable g μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.intro hC fun x hx => by
      by_contra h
      exact hx (hgC x h))
  have hI : Integrable (Function.uncurry fun x y => χ y * (g x * T (j x * j y))) (μ.prod μ) := by
    refine (hgi.norm.mul_prod ((hint _ hK).const_mul M)).mono' ?_ (Eventually.of_forall ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact (hχ.comp continuous_snd).mul ((hg.comp continuous_fst).mul
        (hT.comp ((hj.comp continuous_fst).mul (hj.comp continuous_snd))))
    · rintro ⟨x, y⟩
      simp only [Function.uncurry_apply_pair, norm_mul]
      by_cases hx : g x = 0
      · simp [hx]
      by_cases hy : T (j x * j y) = 0
      · rw [hy, norm_zero, mul_zero, mul_zero]
        exact mul_nonneg (norm_nonneg _) (mul_nonneg hM0 (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _))
      have hmem : j y ∈ (j '' C⁻¹) * tsupport T := by
        refine ⟨j x⁻¹, ⟨x⁻¹, by simpa using hgC x hx, rfl⟩, j x * j y, subset_tsupport _ hy, ?_⟩
        show j x⁻¹ * (j x * j y) = j y
        rw [← hjm, ← hjm, inv_mul_cancel_left]
      rw [Set.indicator_of_mem hmem]
      calc ‖χ y‖ * (‖g x‖ * ‖T (j x * j y)‖) ≤ ‖χ y‖ * (‖g x‖ * M) := by gcongr; exact hM _
        _ = _ := by ring
  rw [← integral_const_mul]
  simp_rw [h1]
  rw [integral_integral_swap hI]
  simp_rw [integral_const_mul]

theorem UpperTheory.schwartz_bruhat_integral_identity :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
        ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure],
        ∀ (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∀ (ν : Chr F E), Continuous ν → ∀ z : ℕ, 1 ≤ z →
        ∀ T₁ ∈ SB (Fv F v ⊗[F] E), ∀ T₂ ∈ SB (Fv F v ⊗[F] E), ∀ C₁ C₂ : Set (idelesAt E (evFin F v)), IsCompact C₁ → IsCompact C₂ →
          (∀ t, four v ψ m T₁ t ≠ 0 → ∃ l ∈ C₁, compFin F E v (l.1 : AE F E) = t) →
          (∀ t, four v ψ m T₂ t ≠ 0 → ∃ l ∈ C₂, compFin F E v (l.1 : AE F E) = t) →
          (∫ l : idelesAt E (evFin F v), T₁ (compFin F E v (l.1 : AE F E)) * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z ∂μ) * (∫ l : idelesAt E (evFin F v), four v ψ m T₂ (compFin F E v (l.1 : AE F E)) *
              (((absE F E l.1 : ℝ) : ℂ) * ((ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z)⁻¹) ∂μ) =
          (∫ l : idelesAt E (evFin F v), T₂ (compFin F E v (l.1 : AE F E)) * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z ∂μ) * (∫ l : idelesAt E (evFin F v), four v ψ m T₁ (compFin F E v (l.1 : AE F E)) *
              (((absE F E l.1 : ℝ) : ℂ) * ((ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z)⁻¹) ∂μ) := by
  intro F E _ _ _ _ _ v ψ hψc hψ _ _ m _ μ hμ ν hν z hz T₁ hT₁ T₂ hT₂ C₁ C₂ hC₁ hC₂ h₁ h₂
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  obtain ⟨c, -, hc⟩ := UpperTheory.local_units_haar_comparison F E v m μ hμ
  set φ := idelesAtEquiv E v with hφ
  have hj : Continuous fun l : idelesAt E (evFin F v) => compFin F E v (l.1 : AE F E) :=
    Units.continuous_val.comp φ.continuous
  have hinj : Function.Injective fun l : idelesAt E (evFin F v) => compFin F E v (l.1 : AE F E) :=
    Units.val_injective.comp φ.injective
  have ha : Continuous fun l : idelesAt E (evFin F v) => ((absE F E l.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      ((GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp continuous_subtype_val))
  have ha0 : ∀ l : idelesAt E (evFin F v), ((absE F E l.1 : ℝ) : ℂ) ≠ 0 := fun l => by
    have : absE F E l.1 ≠ 0 := ((Group.isUnit l.1).map (absE F E)).ne_zero
    exact_mod_cast this
  have key : ∀ T ∈ SB (Fv F v ⊗[F] E), ∀ T' ∈ SB (Fv F v ⊗[F] E), ∀ C : Set (idelesAt E (evFin F v)), IsCompact C →
      (∀ t, four v ψ m T' t ≠ 0 → ∃ l ∈ C, compFin F E v (l.1 : AE F E) = t) →
      (∫ l : idelesAt E (evFin F v), T (compFin F E v (l.1 : AE F E)) * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z ∂μ) *
        (∫ l : idelesAt E (evFin F v), four v ψ m T' (compFin F E v (l.1 : AE F E)) *
          (((absE F E l.1 : ℝ) : ℂ) * ((ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z)⁻¹) ∂μ) =
      ∫ y : idelesAt E (evFin F v), ((ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ z) *
        ((c : ℂ) * ∫ x, four v ψ m T' x * T (x * ((φ y : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) ∂m) ∂μ := by
    intro T hT T' hT' C hC h
    have hf := UpperTheory.fourier_schwartz_bruhat_preserved F E v ψ hψc hψ m T' hT'
    have e := UpperTheory.haar_integral_character_twist μ (fun l : idelesAt E (evFin F v) => compFin F E v (l.1 : AE F E)) hj
      (fun x y => by simp only [Subgroup.coe_mul, Units.val_mul, map_mul])
      (fun l => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z)
      ((continuous_subtype_val.comp (hν.comp continuous_subtype_val)).mul (ha.pow z))
      (fun x y => by
        simp only [Subgroup.coe_mul, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]
        ring)
      (fun x => mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ (ha0 x)))
      (fun K hK => by
        have := GlobalTheory.LocTateInt.integrable_indicator_absE_pow v μ hμ K hK z hz
        simpa only [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, NNReal.norm_eq] using this)
      T hT.1.continuous hT.2
      (fun l => four v ψ m T' (compFin F E v (l.1 : AE F E)) * ((absE F E l.1 : ℝ) : ℂ))
      ((hf.1.continuous.comp hj).mul ha) C hC
      (fun x hx => by
        obtain ⟨l, hl, hlx⟩ := h _ (left_ne_zero_of_mul hx)
        rwa [← hinj hlx])
    simp only [← mul_assoc] at e ⊢
    rw [e]
    congr 1
    funext y
    rw [mul_assoc _ (c : ℂ), ← hc (fun x => four v ψ m T' x * T (x * ((φ y : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)))
      (fun t ht => by
        obtain ⟨l, -, rfl⟩ := h _ (left_ne_zero_of_mul ht)
        exact (φ l).isUnit)]
    congr 2
    funext x
    exact mul_right_comm _ _ _
  rw [key T₁ hT₁ T₂ hT₂ C₂ hC₂ h₂, key T₂ hT₂ T₁ hT₁ C₁ hC₁ h₁]
  congr 1
  funext y
  rw [UpperTheory.fourier_transform_pairing_translate F E v ψ hψc hψ m T₁ hT₁ T₂ hT₂]
