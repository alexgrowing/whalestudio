import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Glob.CharAF

theorem real_char (f : AddChar ℝ ℂ) (hf : Continuous f) (hn : ∀ t, ‖f t‖ = 1) :
    ∃ α : ℝ, ∀ t : ℝ, f t = Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := by
  have hne : ∀ t, f t ≠ 0 := fun t h => by
    have := hn t
    simp [h] at this
  let χ : AddChar ℝ ℂˣ :=
    { toFun := fun t => Units.mk0 (f t) (hne t)
      map_zero_eq_one' := Units.ext (by simp)
      map_add_eq_mul' := fun a b => Units.ext (by simp [AddChar.map_add_eq_mul]) }
  have hχ : Continuous χ := Units.isEmbedding_val₀.continuous_iff.2 hf
  obtain ⟨s, hs, -⟩ := GroundTheory.Global.existsUnique_addChar_real_units χ hχ
  have hs' : ∀ t : ℝ, f t = Complex.exp (s * t) := hs
  have hre : s.re = 0 := by
    have h1 := hn 1
    rw [hs' 1, Complex.norm_exp] at h1
    simpa using h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨s.im / (2 * Real.pi), fun t => ?_⟩
  rw [hs' t]
  congr 1
  have hs2 : s = (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  push_cast
  rw [hs2]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]
  field_simp
  simp
  ring

theorem pi_char {ι : Type} [Fintype ι] [DecidableEq ι] (g : AddChar (ι → ℝ) ℂ) (hg : Continuous g)
    (hn : ∀ x, ‖g x‖ = 1) :
    ∃ α : ι → ℝ, ∀ x, g x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * x w : ℝ) : ℂ)) := by
  have key : ∀ w, ∃ α : ℝ, ∀ t : ℝ, g (Pi.single w t) =
      Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := fun w =>
    real_char (g.compAddMonoidHom (AddMonoidHom.single (fun _ => ℝ) w))
      (show Continuous (fun t : ℝ => g (Pi.single w t)) from hg.comp (continuous_pi fun j => by
        by_cases h : j = w
        · subst h
          simp only [Pi.single_eq_same]
          exact continuous_id
        · simpa [Pi.single_apply, h] using continuous_const)) (fun t => hn _)
  choose α hα using key
  refine ⟨α, fun x => ?_⟩
  have hx : x = ∑ w, Pi.single w (x w) := (Finset.univ_sum_single x).symm
  have hsum : ∀ s : Finset ι, g (∑ w ∈ s, Pi.single w (x w)) = ∏ w ∈ s, g (Pi.single w (x w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx]
  rw [hsum, Finset.prod_congr rfl fun w _ => hα w (x w), ← Complex.exp_sum, ← Finset.mul_sum]
  push_cast
  rfl

theorem places_indep {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (β : InfinitePlace F → ℝ)
    (h : ∀ c : F, ∑ w, β w * ρ w c = 0) : β = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      exact congrArg (fun f : F →* ℝ => ((f x : ℝ) : ℂ)) hww
    rw [← InfinitePlace.mk_embedding w, h1, InfinitePlace.mk_embedding]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  funext w
  refine Fintype.linearIndependent_iff.1 hli β ?_ w
  funext c
  simpa using h c

theorem exists_dual {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (htr : ∀ z : F, ∑ w, ρ w z = ((Algebra.trace ℚ F z : ℚ) : ℝ))
    (α : InfinitePlace F → ℝ) (N : ℕ) (hN : 0 < N)
    (hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n) :
    ∃ a : F, ∀ w, α w = ρ w a := by
  have hrat : ∀ c : F, ∃ q : ℚ, ∑ w, α w * ρ w c = q := by
    intro c
    obtain ⟨y, hy, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, (r : F) = (y : F) * c :=
      ⟨IsIntegralClosure.mk' (𝓞 F) (y • c) hyi,
        (IsIntegralClosure.algebraMap_mk' (𝓞 F) (y • c) hyi).trans (by simp)⟩
    obtain ⟨n, hn⟩ := hint r
    refine ⟨n / (N * y), ?_⟩
    have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 : ∑ w, α w * ρ w ((N : F) * (r : F)) = N * y * ∑ w, α w * ρ w c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hr]
      simp only [map_mul, map_natCast, map_intCast]
      ring
    rw [h1] at hn
    push_cast
    field_simp
    linarith
  choose q hq using hrat
  let L : F →ₗ[ℚ] ℚ :=
    { toFun := q
      map_add' := fun x y => by
        have : ((q (x + y) : ℚ) : ℝ) = ((q x + q y : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, ← hq, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [map_add]
          ring
        exact_mod_cast this
      map_smul' := fun t x => by
        have : ((q (t • x) : ℚ) : ℝ) = ((t * q x : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          have : t • x = (t : F) * x := by simp [Algebra.smul_def]
          rw [this, map_mul, map_ratCast]
          ring
        exact_mod_cast this }
  let a : F := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm L
  have ha : ∀ c, q c = Algebra.trace ℚ F (a * c) := by
    intro c
    have h1 := LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ F) (m := a) (n := c)
    rw [LinearEquiv.apply_symm_apply, Algebra.traceForm_apply] at h1
    exact h1
  refine ⟨a, fun w => ?_⟩
  have h0 : (fun w => α w - ρ w a) = 0 := by
    refine places_indep ρ hρ _ fun c => ?_
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hq c, ha c, ← htr (a * c)]
    simp [map_mul]
  have h1 := congrFun h0 w
  simpa [sub_eq_zero] using h1

theorem exists_char_data : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) ∧ ∃ ψf : AddChar (Af F) ℂ, GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf ∧ ∀ y : Af F, ψ (pairA F 0 y) = ψf (algebraMap F (Af F) a * y) := by
  intro F _ _ hF ρ e hρ he heρ ψ hψ
  classical
  have htr := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ
  have hes : Continuous e.toEquiv.symm := (Equiv.continuous_symm_iff e.toEquiv).2 he.isOpenMap

  let φ : (InfinitePlace F → ℝ) →+ AF F :=
    { toFun := fun x => pairA F (e.symm x) 0
      map_zero' := by
        rw [map_zero]
        rfl
      map_add' := fun x y => by
        rw [map_add]
        exact Prod.ext rfl (add_zero _).symm }
  have hφ : Continuous φ := (hes.prodMk continuous_const : Continuous fun x => (e.symm x, (0 : Af F)))
  obtain ⟨α, hα⟩ := pi_char (ψ.compAddMonoidHom φ) (hψ.1.comp hφ) (fun x => hψ.2.1 _)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * e x w : ℝ) : ℂ)) := fun x => by
    have := hα (e x)
    simpa [φ] using this
  have hsplit : ∀ c : F, ψ (pairA F (algebraMap F (Ainf F) c) 0) *
      ψ (pairA F 0 (algebraMap F (Af F) c)) = 1 := fun c => by
    rw [← AddChar.map_add_eq_mul, ← hψ.2.2.1 c]
    exact congrArg ψ (Prod.ext (add_zero _) (zero_add _))

  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.1 _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  have hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n := by
    intro r
    have hr : algebraMap F (Af F) (r : F) ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F :=
      ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨r, rfl⟩
    have h1 : ψ (pairA F 0 (algebraMap F (Af F) ((N : F) * (r : F)))) = 1 := by
      have := hNU _ hr
      rw [map_mul, map_natCast]
      exact this
    have h2 := hsplit ((N : F) * (r : F))
    rw [h1, mul_one, hinf, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h3 : ((∑ w, α w * e (algebraMap F (Ainf F) ((N : F) * (r : F))) w : ℝ) : ℂ) = n := by
      apply mul_left_cancel₀ hI
      rw [hn]
      ring
    simp only [heρ] at h3
    exact_mod_cast h3
  obtain ⟨a, ha⟩ := exists_dual ρ hρ htr α N hN hint
  have hinf' : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ)) := fun x => by
    rw [hinf]
    simp only [ha]
  have hfin : ∀ c : F, ψ (pairA F 0 (algebraMap F (Af F) c)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ)) := fun c => by
    have h1 := hsplit c
    have h2 : ((∑ w, ρ w a * e (algebraMap F (Ainf F) c) w : ℝ) : ℂ) = ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ) := by
      have h3 := htr (a * c)
      simp only [map_mul] at h3
      simp only [heρ]
      rw [h3]
      push_cast
      rfl
    rw [hinf', h2] at h1
    rw [neg_mul, Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : ∀ x : Ainf F, ψ (pairA F x 0) = 1 := fun x => by
      rw [hinf']
      simp
    have h2 : ∀ y : Af F, ψ (pairA F 0 y) = 1 := by
      intro y
      have hc : Continuous fun y : Af F => ψ (pairA F 0 y) := hψ.1.comp hp
      refine (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.1.induction_on y (isClosed_eq hc continuous_const) fun c => ?_
      rw [hfin]
      simp
    obtain ⟨z, hz⟩ := hψ.2.2.2
    apply hz
    have h3 : z = pairA F z.1 0 + pairA F 0 z.2 := Prod.ext (add_zero _).symm (zero_add _).symm
    rw [h3, AddChar.map_add_eq_mul, h1, h2, one_mul]

  let ψf : AddChar (Af F) ℂ :=
    { toFun := fun y => ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * y))
      map_zero_eq_one' := by
        rw [mul_zero]
        exact ψ.map_zero_eq_one
      map_add_eq_mul' := fun x y => by
        rw [mul_add, ← AddChar.map_add_eq_mul]
        exact congrArg ψ (Prod.ext (add_zero _).symm rfl) }
  refine ⟨a, ha0, hinf', ψf, ⟨?_, fun b => ?_⟩, fun y => ?_⟩
  · exact hψ.1.comp (hp.comp (continuous_const.mul continuous_id))
  · show ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * algebraMap F (Af F) b)) = _
    rw [← map_mul, hfin, mul_inv_cancel_left₀ ha0]
  · show _ = ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * (algebraMap F (Af F) a * y)))
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul]

end GlobalTheory.CompanionTheory.Glob.CharAF
