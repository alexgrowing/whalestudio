import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private abbrev Bx (F : Type) [Field F] [NumberField F] : Set (Fin 2 → A F) := Set.univ.pi fun _ => fundamentalSet F

private theorem vn (q : A E) : (nU q).val = !![1, q; 0, 1] := rfl

private theorem n_add (x y : A E) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem n_zero : gl (nU (0 : A E)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem cont_n : Continuous fun q : A E => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

private theorem rat_n (k : E) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

private theorem ψ_rt (k : F) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

private theorem ψ_neg_mul (x : A F) : ψ (-x) * ψ x = 1 := by
  rw [← ψ_add, neg_add_cancel]
  simpa using ψ_rt (0 : F)

private theorem cont_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

private theorem mkE_add (D : Dat F E) (a b c d : A F) : D.mkE (a + c) (b + d) = D.mkE a b + D.mkE c d := by
  simp only [Dat.mkE, map_add, add_mul]
  abel

private theorem mkE_rat (D : Dat F E) (x y : F) :
    D.mkE (rt x) (rt y) = rt (algebraMap F E x + algebraMap F E y * D.θ) := by
  simp only [Dat.mkE, rt, AdeleBaseChange.adeleMap_algebraMap, map_add, map_mul]

private theorem cont_mkE (D : Dat F E) : Continuous fun x : Fin 2 → A F => D.mkE (x 0) (x 1) :=
  (AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)

private def Jw (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) (x : Fin 2 → A F) : ℂ :=
  Φ (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (2 * x 0)

private theorem cont_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    Continuous (Jw D Φ h) :=
  (hΦ.comp ((cont_n.comp (cont_mkE D)).mul continuous_const)).mul
    (cont_ψ.comp (continuous_const.mul (continuous_apply 0)))

private theorem int_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hΦ : Continuous Φ) (h : GL (Fin 2) (A E)) :
    IntegrableOn (Jw D Φ h) (Bx F) (adeleMeasurePi F) := by
  obtain ⟨B, hB, hEB⟩ : ∃ B, IsCompact B ∧ fundamentalSet F ⊆ B :=
    ⟨closure (fundamentalSetInfinite F) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin 2 => B) := isCompact_univ_pi fun _ => hB
  exact ((cont_J D hΦ h).continuousOn.integrableOn_compact hC).mono_set
    fun x hx i hi => hEB (hx i hi)

private theorem per_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (η : Fin 2 → F) (x : Fin 2 → A F) :
    Jw D Φ h ((fun i => algebraMap F (A F) (η i)) + x) = Jw D Φ h x := by
  obtain ⟨γ, hγ⟩ := rat_n (algebraMap F E (η 0) + algebraMap F E (η 1) * D.θ)
  have e : (2 : A F) * (algebraMap F (A F) (η 0) + x 0) = rt (2 * η 0) + 2 * x 0 := by
    simp only [rt, map_mul, map_ofNat, mul_add]
  simp only [Jw, Pi.add_apply]
  rw [mkE_add, n_add, e, ψ_add, ψ_rt, one_mul]
  change Φ (gl (nU (D.mkE (rt (η 0)) (rt (η 1)))) * gl (nU (D.mkE (x 0) (x 1))) * h) * _ = _
  rw [mkE_rat, ← hγ, mul_assoc, hL]

private theorem shift_J (D : Dat F E) {Φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g)
    (h : GL (Fin 2) (A E)) (a : Fin 2 → A F) :
    ∫ x in Bx F, Jw D Φ h (x + a) ∂(adeleMeasurePi F) = ∫ x in Bx F, Jw D Φ h x ∂(adeleMeasurePi F) :=
  GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add a fun ξ hξ x => by
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    exact per_J D hL h η x

private theorem sum_Tj {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n),
      ∀ G : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * G c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * G c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun G => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_int {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} {X : Type} [MeasurableSpace X]
    (μ : Measure X) (hB : B.card = n) (G : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ)
    (h : ∀ x, Eig w B (G x)) (hi : ∀ y, Integrable (fun x => G x y * a x) μ) :
    Eig w B (fun y => ∫ x, G x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen

end

open UpperTheory.ConvolutionTheory.R2.H.WhittakerCoefficientEigen in
theorem UpperTheory.ConvolutionTheory.R2.H.weEig :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ), Continuous Φ →
      ((∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) → ∀ u t h, WE D Φ (gl (nU (D.mkE u t)) * h) = ψ (-(2 * u)) * WE D Φ h) ∧
      (∀ w B, EigAt w B Φ → EigAt w B (WE D Φ)) ∧
      ∀ (Φ' : GL (Fin 2) (A E) → ℂ) (c : ℂ), Continuous Φ' → ∀ h, WE D (Φ + c • Φ') h = WE D Φ h + c * WE D Φ' h := by
  intro F E _ _ _ _ _ D Φ hΦ
  have eW : ∀ (Ψ : GL (Fin 2) (A E) → ℂ) h, WE D Ψ h = ∫ x in Bx F, Jw D Ψ h x ∂(adeleMeasurePi F) := fun _ _ => rfl
  refine ⟨fun hL u t h => ?_, fun w B hB g => ?_, fun Φ' c hΦ' h => ?_⟩
  · rw [eW, eW, ← shift_J D hL h ![u, t], ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e : (2 : A F) * (x 0 + u) = 2 * x 0 + 2 * u := mul_add _ _ _
    simp only [Jw, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mkE_add, n_add, e, ψ_add, mul_assoc (gl _)]
    linear_combination (-(Φ (gl (nU (D.mkE (x 0) (x 1))) * (gl (nU (D.mkE u t)) * h))) * ψ (2 * x 0)) * ψ_neg_mul (2 * u)
  · refine eig_int ((adeleMeasurePi F).restrict (Bx F)) (hB 1).card
      (fun x y => Φ (gl (nU (D.mkE (x 0) (x 1))) * (g * finGL E 2 (locGL E 2 w y)))) (fun x => ψ (2 * x 0))
      (fun x => ?_) fun y => int_J D hΦ _
    simpa only [mul_assoc] using hB (gl (nU (D.mkE (x 0) (x 1))) * g)
  · rw [eW, eW, eW, ← integral_const_mul, ← integral_add (int_J D hΦ h) ((int_J D hΦ' h).const_mul c)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Jw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
