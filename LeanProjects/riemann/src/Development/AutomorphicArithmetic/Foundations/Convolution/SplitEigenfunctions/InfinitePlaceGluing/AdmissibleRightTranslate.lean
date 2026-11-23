import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerPeriodAddSmulAndNormLe
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsBoundCuspFormOfUnitaryCentralCharacter
import Development.AutomorphicArithmetic.WhittakerHecke.IntegralUnipotentCoordinatesEqZeroOfCuspidal
import Development.AutomorphicArithmetic.WhittakerHecke.ArchimedeanConjugateCurveOneParameterSubgroup
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerCoeffLieDerivUnipotentEqMul
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerCoeffNeZeroFiniteAdeleMemCompact

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem wo_sum (D : Dat ℚ E) {ι : Type} (s : Finset ι) (a : ι → ℂ) (F : ι → GL (Fin 2) (A E) → ℂ)
    (hF : ∀ i, Continuous (F i)) (h : GL (Fin 2) (A E)) :
    Wo D (∑ i ∈ s, a i • F i) h = ∑ i ∈ s, a i * Wo D (F i) h := by
  obtain ⟨hadd, hsmul, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  induction s using Finset.induction_on with
  | empty => simp [Wo]
  | insert i s hi ih =>
    have hc : Continuous (∑ x ∈ s, a x • F x) := by
      rw [Finset.sum_fn]
      exact continuous_finset_sum _ fun j _ => (hF j).const_smul _
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd _ _ ((hF i).const_smul _) hc, hsmul, ih]

private theorem lie_expand {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E 2)) (X : Lie E 2) (f : Sm E 2) :
    (lie E 2 X f).1 = ∑ i, ((b.repr X i : ℝ) : ℂ) • (lie E 2 (b i) f).1 := by
  have h : lie E 2 X = ∑ i, (b.repr X i) • lie E 2 (b i) := by
    conv_lhs => rw [← b.sum_repr X]
    rw [map_sum]
    simp only [map_smul]
  rw [h]
  funext g
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

private theorem pow_bound (D : Dat ℚ E) (P : CuspSub E 2) (hL : ∀ f ∈ P.V, Pp.Lf f.1)
    (hB : ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B) (r : ℕ) :
    ∀ f ∈ P.V, ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ y : (A ℚ)ˣ, ∀ k ∈ C,
      |re (y : A ℚ)| ^ r * ‖Wo D f.1 (em E (aE y) * k)‖ ≤ B := by
  obtain ⟨-, -, hnorm⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  induction r with
  | zero =>
    intro f hf C _
    obtain ⟨B, hB'⟩ := hB f hf
    exact ⟨B, fun y k _ => by simpa using hnorm f.1 B _ hB'⟩
  | succ r ih =>
    intro f hf C hC
    let b := Module.finBasis ℝ (Lie E 2)
    have hmem : ∀ X, lie E 2 X f ∈ P.V := fun X => P.stable (.lie X) f hf
    choose Bi hBi using fun i => ih _ (hmem (b i)) C hC
    have hcont : ∀ i, Continuous fun k : GL (Fin 2) (A E) => b.repr (toL (XB D k)) i := fun i =>
      ((LinearMap.continuous_of_finiteDimensional ((Module.Basis.coord b i))).comp (UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D 1).2.2.2)
    choose R hR using fun i => hC.exists_bound_of_continuousOn (hcont i).continuousOn
    refine ⟨(∑ i, |R i| * |Bi i|) / (2 * Real.pi), fun y k hk => ?_⟩
    have he := UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul E D f (hL f hf) (fun X => ⟨(hL _ (hmem X)).1, hB _ (hmem X)⟩) y k
    rw [lie_expand b, wo_sum D _ _ _ fun i => (hL _ (hmem (b i))).1] at he
    have hpi : 0 < 2 * Real.pi := by positivity
    have h1 : 2 * Real.pi * (|re (y : A ℚ)| * ‖Wo D f.1 (em E (aE y) * k)‖) ≤
        ∑ i, ‖b.repr (toL (XB D k)) i‖ * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖ := by
      have := congrArg norm he
      rw [norm_mul, norm_mul, norm_mul, norm_mul] at this
      simp only [Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one] at this
      rw [mul_assoc] at this
      rw [← this]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      simp
    rw [le_div_iff₀ hpi, pow_succ]
    calc |re (y : A ℚ)| ^ r * |re (y : A ℚ)| * ‖Wo D f.1 (em E (aE y) * k)‖ * (2 * Real.pi)
        = |re (y : A ℚ)| ^ r * (2 * Real.pi * (|re (y : A ℚ)| * ‖Wo D f.1 (em E (aE y) * k)‖)) := by ring
      _ ≤ |re (y : A ℚ)| ^ r * ∑ i, ‖b.repr (toL (XB D k)) i‖ * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖ := by gcongr
      _ = ∑ i, ‖b.repr (toL (XB D k)) i‖ * (|re (y : A ℚ)| ^ r * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, |R i| * |Bi i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 := hBi i y k hk
          have h3 := hR i k hk
          have h4 : 0 ≤ |re (y : A ℚ)| ^ r * ‖Wo D (lie E 2 (b i) f).1 (em E (aE y) * k)‖ := by positivity
          exact mul_le_mul (h3.trans (le_abs_self _)) (h2.trans (le_abs_self _)) h4 (abs_nonneg _)

end SlopeTestRemainingChoices

section Main

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (r : ℕ) : (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ r ≤ 2 ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
      _ ≤ 2 ^ r * (1 + x ^ r) := le_mul_of_one_le_right (by positivity) (by have := pow_nonneg hx r; linarith)
  · calc (1 + x) ^ r ≤ (2 * x) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
      _ = 2 ^ r * x ^ r := mul_pow _ _ _
      _ ≤ 2 ^ r * (1 + x ^ r) := by gcongr; linarith

private theorem wdec_of (D : Dat ℚ E) (P : CuspSub E 2) (hL : ∀ f ∈ P.V, Pp.Lf f.1)
    (hB : ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B) (f : Sm E 2) (hf : f ∈ P.V) (C : Set (GL (Fin 2) (A E))) (hC : IsCompact C) :
    ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ r : ℕ, ∃ B : ℝ,
      ∀ y : (A ℚ)ˣ, ∀ k ∈ C, ‖Wo D f.1 (em E (aE y) * k)‖ ≤ B * ((1 + |re y|) ^ r)⁻¹ ∧
        (Wo D f.1 (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K) := by
  obtain ⟨K, hK, hs⟩ := UpperTheory.whittakerCoeff_ne_zero_finiteAdele_mem_compact E D f (P.cusp f hf).1 (hL f hf) C hC
  refine ⟨K, hK, fun r => ?_⟩
  obtain ⟨B₀, h₀⟩ := pow_bound D P hL hB 0 f hf C hC
  obtain ⟨B₁, h₁⟩ := pow_bound D P hL hB r f hf C hC
  refine ⟨2 ^ r * (B₀ + B₁), fun y k hk => ⟨?_, hs y k hk⟩⟩
  have h0 := h₀ y k hk
  have h1 := h₁ y k hk
  rw [pow_zero, one_mul] at h0
  have hp : 0 < (1 + |re (y : A ℚ)|) ^ r := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  calc ‖Wo D f.1 (em E (aE y) * k)‖ * (1 + |re (y : A ℚ)|) ^ r
      ≤ ‖Wo D f.1 (em E (aE y) * k)‖ * (2 ^ r * (1 + |re (y : A ℚ)| ^ r)) := by
        gcongr
        exact one_add_pow_le _ (abs_nonneg _) r
    _ = 2 ^ r * (‖Wo D f.1 (em E (aE y) * k)‖ + |re (y : A ℚ)| ^ r * ‖Wo D f.1 (em E (aE y) * k)‖) := by ring
    _ ≤ 2 ^ r * (B₀ + B₁) := by gcongr

private def Adm' (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) : Prop :=
  admitted D ω φ ∧ ∀ g, ∫ b in fundamentalSet E, φ (gl (nU b) * g) ∂(adeleMeasure E) = 0

private theorem Adm'.zero' (D : Dat ℚ E) (ω : HChar ℚ) : Adm' D ω (0 : GL (Fin 2) (A E) → ℂ) := by
  refine ⟨⟨continuous_const, fun _ _ => rfl, fun _ _ => by simp, fun _ => by simp, ⟨0, fun _ => by simp⟩,
    fun _ _ _ _ _ => ⟨0, fun _ _ _ _ _ => by simp⟩, fun _ _ => ⟨∅, isCompact_empty, fun _ => ⟨0, fun y k _ => ?_⟩⟩⟩, fun _ => by simp⟩
  have : Wo D (0 : GL (Fin 2) (A E) → ℂ) (em E (aE y) * k) = 0 := by simp [Wo]
  simp [this]

private theorem Adm'.add {D : Dat ℚ E} {ω : HChar ℚ} {φ φ' : GL (Fin 2) (A E) → ℂ} (h : Adm' D ω φ) (h' : Adm' D ω φ') :
    Adm' D ω (φ + φ') := by
  obtain ⟨a, a0⟩ := h
  obtain ⟨b, b0⟩ := h'
  have hc : Continuous (φ + φ') := a.cont.add b.cont
  have hl : ∀ γ g, (φ + φ') (ratGL E 2 γ * g) = (φ + φ') g := fun γ g => by simp [a.left, b.left]
  have hz : ∀ g, ∫ x in fundamentalSet E, (φ + φ') (gl (nU x) * g) ∂(adeleMeasure E) = 0 := fun g => by
    have hi : ∀ {u : GL (Fin 2) (A E) → ℂ}, Continuous u → IntegrableOn (fun x => u (gl (nU x) * g)) (fundamentalSet E) (adeleMeasure E) :=
      fun hu => Pp.intOn (hu.comp (Pp.cont_n.mul continuous_const))
    simp only [Pi.add_apply]
    rw [integral_add (hi a.cont) (hi b.cont), a0, b0, add_zero]
  refine ⟨⟨hc, hl, fun z g => by simp [a.cen, b.cen, mul_add], UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal E D _ ⟨hc, hl⟩ hz, ?_, ?_, ?_⟩, hz⟩
  · obtain ⟨B, hB⟩ := a.bdd
    obtain ⟨B', hB'⟩ := b.bdd
    exact ⟨B + B', fun g => (norm_add_le _ _).trans (add_le_add (hB g) (hB' g))⟩
  · intro C hC c hc r
    obtain ⟨B, hB⟩ := a.decay C hC c hc r
    obtain ⟨B', hB'⟩ := b.decay C hC c hc r
    refine ⟨B + B', fun x y k hk hy => ?_⟩
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hB x y k hk hy) (hB' x y k hk hy))
  · intro C hC
    obtain ⟨K, hK, h⟩ := a.wdec C hC
    obtain ⟨K', hK', h'⟩ := b.wdec C hC
    refine ⟨K ∪ K', hK.union hK', fun r => ?_⟩
    obtain ⟨B, hB⟩ := h r
    obtain ⟨B', hB'⟩ := h' r
    refine ⟨B + B', fun y k hk => ?_⟩
    have e := (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).1 φ φ' a.cont b.cont (em E (aE y) * k)
    obtain ⟨u, v⟩ := hB y k hk
    obtain ⟨u', v'⟩ := hB' y k hk
    rw [e, add_mul]
    refine ⟨(norm_add_le _ _).trans (add_le_add u u'), fun hne => ?_⟩
    by_cases h0 : Wo D φ (em E (aE y) * k) = 0
    · exact Or.inr (v' fun h1 => hne (by rw [h0, h1, add_zero]))
    · exact Or.inl (v h0)

private theorem Adm'.smul {D : Dat ℚ E} {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (c : ℂ) (h : Adm' D ω φ) :
    Adm' D ω (c • φ) := by
  obtain ⟨a, a0⟩ := h
  have hc : Continuous (c • φ) := a.cont.const_smul c
  have hl : ∀ γ g, (c • φ) (ratGL E 2 γ * g) = (c • φ) g := fun γ g => by simp [a.left]
  have hz : ∀ g, ∫ x in fundamentalSet E, (c • φ) (gl (nU x) * g) ∂(adeleMeasure E) = 0 := fun g => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, a0, mul_zero]
  refine ⟨⟨hc, hl, fun z g => by simp [a.cen, mul_left_comm], UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal E D _ ⟨hc, hl⟩ hz, ?_, ?_, ?_⟩, hz⟩
  · obtain ⟨B, hB⟩ := a.bdd
    refine ⟨‖c‖ * B, fun g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB g) (norm_nonneg _)
  · intro C hC c' hc' r
    obtain ⟨B, hB⟩ := a.decay C hC c' hc' r
    refine ⟨‖c‖ * B, fun x y k hk hy => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB x y k hk hy) (norm_nonneg _)
  · intro C hC
    obtain ⟨K, hK, h⟩ := a.wdec C hC
    refine ⟨K, hK, fun r => ?_⟩
    obtain ⟨B, hB⟩ := h r
    refine ⟨‖c‖ * B, fun y k hk => ?_⟩
    obtain ⟨u, v⟩ := hB y k hk
    have e := (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.1 c φ (em E (aE y) * k)
    rw [e, norm_mul, mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_left u (norm_nonneg _), fun hne => v (right_ne_zero_of_mul hne)⟩

private theorem wo_translate (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ) (h g : GL (Fin 2) (A E)) :
    Wo D (fun x => f (x * h)) g = Wo D f (g * h) := by
  simp only [Wo, mul_assoc]

private theorem admissible_two_sided_translate (hD : DecE) (D : Dat ℚ E) (P : CuspSub E 2) (ω : HChar ℚ) (hc : CenN P ω) (hu : Unit1 ω)
    (f : Sm E 2) (hf : f ∈ P.V) (h : GL (Fin 2) (A E)) : Adm' D ω fun g => f.1 (g * h) := by
  have hL : ∀ f ∈ P.V, Pp.Lf f.1 := fun f hf => (hD E P f hf).1
  have hB : ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B := UpperTheory.exists_bound_cuspForm_of_unitary_centralCharacter E P ω hc hu
  obtain ⟨hl, h0, hd⟩ := hD E P f hf
  have hcp : ∀ {C : Set (GL (Fin 2) (A E))}, IsCompact C → IsCompact ((· * h) '' C) := fun hC => hC.image (continuous_mul_right h)
  have hz : ∀ g, ∫ b in fundamentalSet E, f.1 (gl (nU b) * g * h) ∂(adeleMeasure E) = 0 := fun g => by
    simp only [mul_assoc]
    exact h0 _
  have hc' : Continuous fun g => f.1 (g * h) := hl.1.comp (continuous_mul_right h)
  have hl' : ∀ γ g, f.1 (ratGL E 2 γ * g * h) = f.1 (g * h) := fun γ g => by rw [mul_assoc, hl.2]
  refine ⟨⟨hc', hl', fun z g => ?_, UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal E D _ ⟨hc', hl'⟩ hz, ?_, ?_, ?_⟩, hz⟩
  · rw [mul_assoc, hc f hf]
  · obtain ⟨B, hB'⟩ := hB f hf
    exact ⟨B, fun g => hB' _⟩
  · intro C hC c hc r
    obtain ⟨B, hB'⟩ := hd _ (hcp hC) c hc r
    refine ⟨B, fun b a k hk ha => ?_⟩
    rw [mul_assoc]
    exact hB' b a _ ⟨k, hk, rfl⟩ ha
  · intro C hC
    obtain ⟨K, hK, hr⟩ := wdec_of D P hL hB f hf _ (hcp hC)
    refine ⟨K, hK, fun r => ?_⟩
    obtain ⟨B, hB'⟩ := hr r
    refine ⟨B, fun y k hk => ?_⟩
    simp only [wo_translate, mul_assoc]
    simpa only [mul_assoc] using hB' y (k * h) ⟨k, hk, rfl⟩

end Main

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.trAdm_of :
    DecE → TrAdm := by
  intro hD E _ _ _ D P ω χ hc hu _ φ hφ
  refine (Submodule.span_induction (p := fun φ _ => Adm' D ω φ) ?_ (Adm'.zero' D ω) (fun _ _ _ _ a b => a.add b)
    (fun c _ _ a => a.smul c) hφ).1
  rintro _ ⟨f, hf, h, rfl⟩
  exact admissible_two_sided_translate hD D P ω hc hu f hf h
